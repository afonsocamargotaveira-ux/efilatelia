"""
Agregador de leilões de selos (somente leilões EM ANDAMENTO)

Executar:
    pip install streamlit requests beautifulsoup4 pandas
    streamlit run app.py

Fonte principal: portal LeilõesBR, endpoint "busca_andamento.asp" (busca apenas em
leilões em andamento). O portal reúne várias casas filatélicas (Filatélica BH,
Galeria Filatélica e Numismática, Cida Mello, Coins e Stamps, Moeda e Selo,
Universo das Coleções, Inovar, etc.).
"""

from __future__ import annotations

import base64
import html
import io
import json
import re
import time
import unicodedata
from concurrent.futures import ThreadPoolExecutor, as_completed
from concurrent.futures import TimeoutError as FutTimeout
from dataclasses import dataclass
from dataclasses import asdict
from pathlib import Path
from urllib.parse import quote, quote_plus, urljoin, urlparse
from urllib.robotparser import RobotFileParser

import pandas as pd
import requests
import streamlit as st
from bs4 import BeautifulSoup

HEADERS = {
    "User-Agent": (
        "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
        "(KHTML, like Gecko) Chrome/124.0 Safari/537.36"
    ),
    "Accept-Language": "pt-BR,pt;q=0.9,en;q=0.8",
}
TIMEOUT = (6, 15)  # (conexão, leitura) em segundos

ENCERRADO = re.compile(
    r"\b(encerrad[oa]|finalizad[oa]|vendid[oa]|arrematad[oa]|ended|closed|sold)\b",
    re.IGNORECASE,
)
# Indícios, na página do lote, de que o leilão já acabou
ENCERRADO_NA_PAGINA = re.compile(
    r"(lote vendido|lote encerrado|leil[aã]o (encerrado|finalizado)|"
    r"venda p[óo]s preg[aã]o|auction (has )?ended)",
    re.IGNORECASE,
)


@dataclass
class Site:
    nome: str
    url_busca: str            # use {q} para o termo e (opcional) {pag} para a página
    seletor_link: str         # seletor CSS dos <a> que apontam para cada lote
    encoding: str = "utf-8"   # codificação usada na query string
    usa_paginas: bool = False # True se a URL tiver {pag}
    grupo: str = ""          # nome exibido nos resultados (agrupa várias categorias)
    busca_local: bool = False # True: o site não filtra por termo; baixamos as páginas e filtramos aqui
    filtro_ativos: str = ""   # filtro especial de "leilão em andamento" (ex.: "philasearch")
    sessao: bool = False      # True: visita a home antes (cookies) e envia Referer
    js: bool = False          # True: a página precisa de JavaScript (usa Playwright, se ativado)
    extra: bool = False       # True: site adicionado pelo usuário (salvo em sites_extras.json)
    pag_1_vazia: bool = False # True: na 1ª página, {pag} vira texto vazio (ex.: "page=")
    href_exige: str = ""      # regex: só links cujo endereço combine (ex.: páginas de produto)
    href_exclui: str = ""     # regex: descarta links de menu, categorias, carrinho etc.
    ativo: bool = True


SITES_PADRAO = [
    *[
        Site(
            nome=f"LeilõesBR · {cat}",
            grupo="LeilõesBR (leilões em andamento)",
            # busca_andamento = só leilões ativos; tp=|HEX| = categoria (nome em Latin-1
            # hexadecimal, exatamente como nos links de categoria do próprio portal)
            url_busca=(
                "https://www.leiloesbr.com.br/busca_andamento.asp"
                "?pesquisa={q}&gbl=0&tp=|" + cat.encode("latin-1").hex().upper() + "|&pag={pag}"
            ),
            seletor_link='a[href*="abre_catalogo.asp?t=1"]',
            encoding="latin-1",
            usa_paginas=True,
            ativo=ativo,
        )
        for cat, ativo in [
            ("Filatelia", True),
            ("Filatelia Brasileira", True),
            ("Filatelia estrangeira", True),
            ("Filatelia Fiscal", False),
        ]
    ],
    Site(
        nome="Philasearch (leilões internacionais)",
        grupo="Philasearch (leilões internacionais)",
        url_busca=(
            "https://www.philasearch.com/en/lots?page={pag}&set_gesetz_bestaetigt_jn=J"
            "&gesetz_bestaetigt_neu=J&set_sprache=en&suchtext={q}"
        ),
        seletor_link='a[href*="posdetail"], a[href*="info.php3?losnr"], a[href*="/i_"]',
        usa_paginas=True,
        filtro_ativos="philasearch",
        sessao=True,
        pag_1_vazia=True,
        js=True,
    ),
    Site(
        nome="eBay – selos (só leilões)",
        grupo="eBay – selos (só leilões)",
        # _sacat=260 = categoria Stamps; LH_Auction=1 = somente leilões; _sop=1 = terminam primeiro
        url_busca="https://www.ebay.com/sch/i.html?_nkw={q}&_sacat=260&LH_Auction=1&_sop=1&_pgn={pag}",
        seletor_link='a[href*="/itm/"]',
        usa_paginas=True,
        js=True,
    ),
    Site(
        nome="Catawiki – selos (leilões online)",
        grupo="Catawiki – selos (leilões online)",
        url_busca="https://www.catawiki.com/en/s?q={q}&page={pag}",
        seletor_link='a[href*="/en/l/"]',
        usa_paginas=True,
        js=True,
    ),
    Site(
        nome="Delcampe – selos",
        grupo="Delcampe – selos",
        url_busca="https://www.delcampe.net/en_US/collectibles/search?term={q}&page={pag}",
        seletor_link='a[href*="/collectibles/"][href$=".html"]',
        usa_paginas=True,
        js=True,
    ),
    Site(
        nome="HipStamp – leilões de selos",
        grupo="HipStamp – leilões de selos",
        # listing_type=auction = só leilões; sort=ending_asc = terminam primeiro
        url_busca=(
            "https://www.hipstamp.com/browse/?keywords={q}&listing_type=auction"
            "&sort=ending_asc&page={pag}"
        ),
        seletor_link='a[href*="/listing/"]',
        usa_paginas=True,
    ),
    # --- Candidatos internacionais: padrões de URL NÃO verificados. Se o app não conseguir
    # --- ler, o link de busca manual aparece na lista "Sites que o app não conseguiu ler".
    Site(
        nome="Invaluable (leilões de selos)",
        grupo="Invaluable (leilões de selos)",
        url_busca="https://www.invaluable.com/search?keyword={q}&upcoming=true&page={pag}",
        seletor_link='a[href*="/auction-lot/"]',
        usa_paginas=True,
        busca_local=True,
        js=True,
    ),
    Site(
        nome="LiveAuctioneers (leilões de selos)",
        grupo="LiveAuctioneers (leilões de selos)",
        url_busca="https://www.liveauctioneers.com/search/?keyword={q}&page={pag}",
        seletor_link='a[href*="/item/"]',
        usa_paginas=True,
        busca_local=True,
        js=True,
    ),
    Site(
        nome="The Saleroom (leilões de selos)",
        grupo="The Saleroom (leilões de selos)",
        url_busca="https://www.the-saleroom.com/en-gb/search-filter?searchterm={q}&page={pag}",
        seletor_link='a[href*="/auction-catalogues/"]',
        usa_paginas=True,
        busca_local=True,
        js=True,
    ),
    Site(
        nome="Loja de Selos (venda direta, NÃO é leilão)",
        # Listagem paginada por ?mpage=N. Como não sabemos o parâmetro de busca do site,
        # baixamos as páginas e filtramos pelo termo aqui (busca_local=True).
        url_busca="https://www.lojadeselos.com.br/produtos/?mpage={pag}",
        seletor_link='a[href*="produto"]',
        usa_paginas=True,
        busca_local=True,
        href_exige=r"/produtos?/[^/?#]+",
        href_exclui=r"(mpage=|categoria|carrinho|checkout|login|conta|contato|sobre|"
                    r"politica|termos|blog|whatsapp|mailto:|tel:|/busca)",
    ),
    Site(
        nome="e-filatelia (AJUSTAR URL E SELETOR)",
        url_busca="https://www.e-filatelia.com/busca?q={q}",  # <-- confirme a URL real
        seletor_link="a[href]",
        ativo=False,
    ),
]


# ----------------------------------------------------------------------------
# Utilidades
# ----------------------------------------------------------------------------
def norm(s: str) -> str:
    s = unicodedata.normalize("NFKD", s)
    return "".join(c for c in s if not unicodedata.combining(c)).lower()


_LINK_PORTAL = re.compile(
    r"abre_catalogo\.asp\?t=1\|(?P<site>https?://[^|]+)\|(?P<leilao>\d+)\|(?P<lote>\d+)",
    re.IGNORECASE,
)


def link_direto_do_lote(link_portal: str) -> str:
    """
    O portal usa links como  abre_catalogo.asp?t=1|http://site|65404|32697493
    (com caracteres '|'), que o servidor rejeita quando o navegador os codifica
    ("The custom error module does not recognize this error").
    Convertemos para a página do lote no site da própria casa de leilões:
        http://site/peca.asp?ID=32697493
    """
    m = _LINK_PORTAL.search(link_portal)
    if not m:
        return link_portal.replace("|", "%7C")
    return f"{m.group('site').rstrip('/')}/peca.asp?ID={m.group('lote')}"


def md_seguro(texto: str) -> str:
    """Escapa caracteres que quebrariam o texto de um link em Markdown."""
    return re.sub(r"([\[\]])", r"\\\1", texto)


PALAVRAS_SELO = re.compile(
    r"\b(selos?|filatel\w*|rhm|yvert|scott|michel|stanley gibbons|sg\s?\d+|"
    r"bloco|blocos|s[ée]rie|olho[s]? de boi|olho de cabra|olho de gato|"
    r"stamps?|briefmarken?|timbres?|sellos?|francobolli|"
    r"carimbo|obliterad\w*|charneira|picote|dentado|sobrecarga|"
    r"inteiro postal|primeiro dia|fdc|aerograma|vinheta)\b",
    re.IGNORECASE,
)


# Itens que aparecem em categorias/lojas de filatelia mas não são selos.
# OUTROS: descartados, a menos que o título cite selo/filatelia (ex.: "moeda e selo")
NAO_SELO = re.compile(
    r"\b(moedas?|c[eé]dulas?|notas? de|medalhas?|condecora\w*|rel[oó]gios?|joias?|semi ?joias?|"
    r"an[eé]is|anel|colar|brincos?|pulseiras?|prata|ouro|pedras?|esmeralda|turmalina|ametista|"
    r"bonecos?|brinquedos?|figuras?|a[cç][aã]o|disco|vinil|lp|gibis?|hq|quadrinhos|revistas?|"
    r"livros?|quadros?|pinturas?|gravuras?|esculturas?|tapetes?|m[oó]veis|mesa|cadeira|"
    r"porcelana|vidro|cristal|canetas?|fichas?|tokens?|kit misto)\b",
    re.IGNORECASE,
)
# ACESSÓRIOS: sempre descartados (mesmo citando "selos", ex.: "álbum para selos")
ACESSORIOS = re.compile(
    r"\b([aá]lbum|[aá]lbuns|classificador\w*|pin[cç]as?|lupas?|protetor\w*|suplementos?|"
    r"cat[aá]logos?|estojos?|acess[oó]rios?|material filat[eé]lico|charneiras?\s+(para|de)|"
    r"folhas? (para|de) [aá]lbum)\b",
    re.IGNORECASE,
)


def passa_filtro_selo(titulo: str, rigor: str) -> bool:
    if rigor.startswith("Desligado"):
        return True
    t = norm(titulo)
    if ACESSORIOS.search(t):
        return False
    tem_selo = bool(PALAVRAS_SELO.search(t))
    if rigor.startswith("Estrito"):
        return tem_selo
    # Moderado: descarta o que parece outro tipo de item, a menos que cite selo/filatelia
    return tem_selo or not NAO_SELO.search(t)


@st.cache_data(ttl=600, show_spinner=False)
def philasearch_leiloes_atuais():
    """
    Lê a home do Philasearch e devolve {id_da_casa: {números dos leilões atuais}}
    a partir da seção "Current Auctions" (leilões marcados como atuais/ao vivo).
    Um número None significa "leilão atual sem número identificável no título".
    """
    try:
        r = requests.get("https://www.philasearch.com/en", headers=HEADERS, timeout=TIMEOUT)
        r.raise_for_status()
    except requests.RequestException:
        return None
    h = r.text
    ini = h.find("Current Auctions")
    fins = [x for x in (h.find("Special fixed priced sales"),
                        h.find("Auction Results and After Auction Sale")) if x > ini]
    if ini < 0 or not fins:
        return None
    trecho = h[ini:min(fins)]
    atuais: dict[str, set] = {}
    for m in re.finditer(r'href="[^"]*?/cat/\d+_(\d+)/[^"]*"[^>]*>(.*?)</a>', trecho, re.S):
        casa, txt = m.group(1), re.sub(r"<[^>]+>", " ", m.group(2))
        # os títulos começam com a data ("Oct. 4th, 2026 ..."): ignora tudo até o ano
        depois_do_ano = re.split(r"20\d\d", txt, maxsplit=1)[-1]
        n = re.search(r"(\d+)\s*(?:st|nd|rd|th)\b|#(\d+)", depois_do_ano)
        num = int(n.group(1) or n.group(2)) if n else None
        atuais.setdefault(casa, set()).add(num)
    return atuais or None


def philasearch_ativo(link: str, atuais) -> bool:
    """Mantém o lote só se a casa tem leilão atual (e, quando dá para comparar, o mesmo nº)."""
    if atuais is None:
        return True
    m = re.search(r"/i_(\d+)-A(\d+)-", link)
    if not m:
        return True  # formato desconhecido: na dúvida, mantém
    casa, num = m.group(1), int(m.group(2))
    nums = atuais.get(casa)
    if nums is None:
        return False          # casa sem leilão em andamento
    if None in nums or num >= 100000:
        return True           # não dá para comparar com segurança
    return num in nums


def termos_no_titulo(titulo: str, consulta: str) -> bool:
    t = norm(titulo)
    return all(term in t for term in norm(consulta).split())


@st.cache_resource
def _robots(base: str):
    """
    Lê o robots.txt com o mesmo User-Agent do app. Se não houver um robots.txt acessível
    (erro de rede, 403, 404...), considera que não há restrições declaradas — o
    RobotFileParser padrão trata 401/403 como "proibido tudo", o que bloqueava sites
    que apenas recusam o User-Agent do Python.
    """
    try:
        r = requests.get(urljoin(base, "/robots.txt"), headers=HEADERS, timeout=TIMEOUT)
    except requests.RequestException:
        return None
    if r.status_code != 200:
        return None
    rp = RobotFileParser()
    rp.parse(r.text.splitlines())
    return rp


def permitido(url: str) -> bool:
    p = urlparse(url)
    rp = _robots(f"{p.scheme}://{p.netloc}")
    return True if rp is None else rp.can_fetch(HEADERS["User-Agent"], url)


@st.cache_resource
def _sessao(base_home: str) -> requests.Session:
    """Sessão com cookies: alguns sites redirecionam para a home quem chega sem cookie."""
    sess = requests.Session()
    sess.headers.update(HEADERS)
    try:
        sess.get(base_home, timeout=TIMEOUT)
    except requests.RequestException:
        pass
    return sess


def baixar_com_navegador(url: str) -> tuple[str, str]:
    """Abre a página num Chromium invisível (Playwright) e devolve (html, url_final)."""
    from playwright.sync_api import sync_playwright  # pip install playwright

    with sync_playwright() as pw:
        navegador = pw.chromium.launch(headless=True)
        try:
            pagina = navegador.new_page(user_agent=HEADERS["User-Agent"], locale="en-US")
            pagina.goto(url, wait_until="domcontentloaded", timeout=30000)
            try:
                pagina.wait_for_load_state("networkidle", timeout=8000)
            except Exception:
                pass  # alguns sites nunca ficam "ociosos"; segue com o que carregou
            return pagina.content(), pagina.url
        finally:
            navegador.close()


def buscar_pagina(site: Site, consulta: str, pag: int, respeitar_robots: bool,
                  usar_navegador: bool = False):
    """Baixa uma página de resultados e devolve (itens, diagnóstico)."""
    url = site.url_busca.format(
        q=quote_plus(consulta, encoding=site.encoding),
        pag="" if (site.pag_1_vazia and pag == 1) else pag,
    )
    diag = {"url": url, "url_final": "", "status": None, "bytes": 0, "links": 0,
            "erro": None, "html": ""}

    if respeitar_robots and not permitido(url):
        diag["erro"] = "Bloqueado pelo robots.txt (desmarque a opção na barra lateral para testar)"
        return [], diag
    try:
        if site.js and usar_navegador:
            texto_html, diag["url_final"] = baixar_com_navegador(url)
            conteudo = texto_html.encode("utf-8")
            diag["status"] = 200
            diag["bytes"] = len(conteudo)
        else:
            if site.sessao:
                p_ = urlparse(url)
                home = f"{p_.scheme}://{p_.netloc}/en"
                r = _sessao(home).get(url, headers={**HEADERS, "Referer": home}, timeout=TIMEOUT)
            else:
                r = requests.get(url, headers=HEADERS, timeout=TIMEOUT)
            diag["url_final"] = r.url
            diag["status"] = r.status_code
            diag["bytes"] = len(r.content)
            r.raise_for_status()
            conteudo, texto_html = r.content, r.text
    except ImportError:
        diag["erro"] = ("Playwright não instalado. Rode: pip install playwright && "
                        "playwright install chromium")
        return [], diag
    except requests.RequestException as e:
        diag["erro"] = f"Falha na requisição: {e}"
        return [], diag
    except Exception as e:  # falhas do navegador automatizado
        diag["erro"] = f"Falha no navegador automatizado: {e}"
        return [], diag

    # o portal declara ISO-8859-1; deixa o requests/bs4 detectarem
    soup = BeautifulSoup(conteudo, "html.parser")
    diag["html"] = texto_html[:3000]

    itens, vistos = [], set()
    for a in soup.select(site.seletor_link):
        href = a.get("href", "")
        if not href or href.startswith(("javascript", "#")):
            continue
        link = urljoin(url, href)
        if site.href_exige and not re.search(site.href_exige, link, re.IGNORECASE):
            continue
        if site.href_exclui and re.search(site.href_exclui, link, re.IGNORECASE):
            continue
        img = a.find("img")
        titulo = (a.get("title") or a.get_text(" ", strip=True)
                  or (img.get("alt") if img else "") or "").strip()
        titulo = re.split(r"\s::\s", titulo)[0]  # "título :: vendedor"
        titulo = re.sub(r"(Opens in a new window or tab|New Listing|Novo anúncio)", "",
                        titulo, flags=re.IGNORECASE).strip()
        if len(titulo) < 6 or link in vistos:  # ignora "Ver", "Comprar", "Home"...
            continue
        vistos.add(link)
        itens.append(
            {
                "Título": re.sub(r"\s+", " ", titulo),
                "Link": link_direto_do_lote(link),
                "Link do portal": link,
            }
        )
    # Fallback: o seletor CSS não achou nada (HTML mudou?). Varre todos os links da página
    # e mantém só os que citam todos os termos buscados no texto/título.
    if not itens:
        for a in soup.find_all("a", href=True):
            href = a["href"]
            if href.startswith(("javascript", "#", "mailto:", "tel:")):
                continue
            img = a.find("img")
            titulo = (a.get("title") or a.get_text(" ", strip=True)
                      or (img.get("alt") if img else "") or "").strip()
            link = urljoin(url, href)
            if len(titulo) < 6 or link in vistos or not termos_no_titulo(titulo, consulta):
                continue
            vistos.add(link)
            itens.append({"Título": re.sub(r"\s+", " ", titulo),
                          "Link": link_direto_do_lote(link), "Link do portal": link})
        diag["fallback"] = bool(itens)
    diag["links"] = len(itens)
    return itens, diag


ARQUIVO_EXTRAS = Path(__file__).with_name("sites_extras.json")


def site_a_partir_de_url(nome: str, url: str, termo: str, js: bool = False) -> tuple[Site, str]:
    """
    Cria um Site a partir de uma URL de resultados de busca copiada do navegador.
    Troca o termo usado no exemplo por {q} e o número da página por {pag}.
    Devolve (site, explicação).
    """
    url = url.strip()
    termo = termo.strip()
    u = url.replace("{", "{{").replace("}", "}}")  # protege chaves para o .format()
    encoding, achou = "utf-8", False
    variantes = [
        (quote_plus(termo), "utf-8"), (quote(termo), "utf-8"),
        (quote_plus(termo, encoding="latin-1"), "latin-1"),
        (quote(termo, encoding="latin-1"), "latin-1"),
        (termo, "utf-8"), (termo.replace(" ", "-"), "utf-8"), (termo.replace(" ", "_"), "utf-8"),
    ]
    for v, enc in sorted(variantes, key=lambda x: -len(x[0])):
        if v and re.search(re.escape(v), u, re.IGNORECASE):
            u = re.sub(re.escape(v), "{q}", u, count=1, flags=re.IGNORECASE)
            encoding, achou = enc, True
            break
    m = re.search(r"([?&](?:page|pag|pagina|pg|p|_pgn|mpage|pageno|pn)=)(\d*)", u, re.IGNORECASE)
    usa_pag = bool(m)
    if m:
        u = u[:m.start(2)] + "{pag}" + u[m.end(2):]
    site = Site(
        nome=nome, grupo=nome, url_busca=u, seletor_link="a[href]", encoding=encoding,
        usa_paginas=usa_pag, js=js, busca_local=True, extra=True,
    )
    msg = (
        f"Modelo criado: `{u}`  \n"
        + ("✔ termo de busca reconhecido → {q}. " if achou else
           "⚠ não encontrei o termo na URL; confira se digitou o mesmo termo usado nela. ")
        + ("✔ paginação reconhecida → {pag}." if usa_pag else "Sem paginação reconhecida (só a 1ª página).")
    )
    return site, msg


def carregar_extras() -> list[Site]:
    try:
        dados = json.loads(ARQUIVO_EXTRAS.read_text(encoding="utf-8"))
        return [Site(**d) for d in dados]
    except Exception:
        return []


def salvar_extras(sites: list[Site]) -> None:
    try:
        ARQUIVO_EXTRAS.write_text(
            json.dumps([asdict(x) for x in sites if x.extra], ensure_ascii=False, indent=2),
            encoding="utf-8",
        )
    except OSError:
        pass


def url_busca_manual(site: Site, consulta: str) -> str:
    return site.url_busca.format(
        q=quote_plus(consulta, encoding=site.encoding),
        pag="" if site.pag_1_vazia else 1,
    )


def lote_ativo(link: str) -> bool:
    """Confere na página do lote se ele não aparece como vendido/encerrado."""
    try:
        r = requests.get(link, headers=HEADERS, timeout=TIMEOUT)
        return not ENCERRADO_NA_PAGINA.search(r.text)
    except requests.RequestException:
        return True  # na dúvida, mantém


def novo_stats(nome: str) -> dict:
    return {
        "Site": nome, "HTTP": None, "Bytes": 0, "Links achados": 0,
        "Descartados (título)": 0, "Descartados (não é selo)": 0,
        "Descartados (encerrado)": 0, "Mantidos": 0, "Tempo (s)": 0.0,
        "Erro": "", "URL": "", "URL final": "", "_html": "", "_amostra": [],
    }


def processar_site(site: Site, consulta: str, max_paginas: int,
                   respeitar_robots: bool, exigir_titulo: bool, verificar: bool,
                   rigor: str = "Moderado", usar_navegador: bool = False,
                   limite_s: int = 45):
    t0 = time.monotonic()
    resultados, vistos = [], set()
    stats = novo_stats(site.nome)
    paginas = max_paginas if site.usa_paginas else 1
    atuais = philasearch_leiloes_atuais() if site.filtro_ativos == "philasearch" else None

    for pag in range(1, paginas + 1):
        if time.monotonic() - t0 > limite_s:
            stats["Erro"] = (f"Tempo máximo de {limite_s}s atingido antes da página {pag} "
                             "(resultados parciais)")
            break
        itens, d = buscar_pagina(site, consulta, pag, respeitar_robots, usar_navegador)
        if pag == 1:
            stats.update({"HTTP": d["status"], "Bytes": d["bytes"],
                          "URL": d["url"], "URL final": d["url_final"],
                          "_html": d["html"]})
        if d["erro"]:
            stats["Erro"] = d["erro"]
            break
        novos = [i for i in itens if i["Link"] not in vistos]
        if not novos:  # página repetida/vazia -> fim da paginação
            break
        for i in novos:
            vistos.add(i["Link"])
        stats["Links achados"] += len(novos)

        for i in novos:
            if (exigir_titulo or site.busca_local) and not termos_no_titulo(i["Título"], consulta):
                stats["Descartados (título)"] += 1
                if len(stats["_amostra"]) < 6:
                    stats["_amostra"].append(i["Título"][:140])
                continue
            if site.filtro_ativos == "philasearch" and not philasearch_ativo(i["Link"], atuais):
                stats["Descartados (encerrado)"] += 1
                continue
            if not passa_filtro_selo(i["Título"], rigor):
                stats["Descartados (não é selo)"] += 1
                continue
            if ENCERRADO.search(i["Título"]):
                stats["Descartados (encerrado)"] += 1
                continue
            resultados.append({"Site": site.grupo or site.nome, **i})
        time.sleep(0.5)

    if verificar and resultados and time.monotonic() - t0 < limite_s:
        # confere no máximo 40 lotes por site, para não travar
        with ThreadPoolExecutor(max_workers=6) as ex:
            ok = list(ex.map(lambda x: lote_ativo(x["Link"]), resultados[:40]))
        ok += [True] * (len(resultados) - len(ok))
        antes = len(resultados)
        resultados = [r for r, o in zip(resultados, ok) if o]
        stats["Descartados (encerrado)"] += antes - len(resultados)

    stats["Mantidos"] = len(resultados)
    stats["Tempo (s)"] = round(time.monotonic() - t0, 1)
    return resultados, stats


# ----------------------------------------------------------------------------
# Interface
# ----------------------------------------------------------------------------
# ----------------------------------------------------------------------------
# Identidade visual eFilatelia: branco, laranja e azul-marinho
# ----------------------------------------------------------------------------
LOGO_SVG = r"""<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 296 66" role="img" aria-label="eFilatelia">
  <title>eFilatelia</title>
  <g transform="translate(4,4)">
  <rect width="48" height="58" fill="#0B1F3A"/>
  <rect x="6" y="6" width="36" height="46" rx="1.5" fill="#FFFFFF"/>
  <g fill="#FFFFFF"><circle cx="4" cy="0" r="2.5"/><circle cx="4" cy="58" r="2.5"/><circle cx="12" cy="0" r="2.5"/><circle cx="12" cy="58" r="2.5"/><circle cx="20" cy="0" r="2.5"/><circle cx="20" cy="58" r="2.5"/><circle cx="28" cy="0" r="2.5"/><circle cx="28" cy="58" r="2.5"/><circle cx="36" cy="0" r="2.5"/><circle cx="36" cy="58" r="2.5"/><circle cx="44" cy="0" r="2.5"/><circle cx="44" cy="58" r="2.5"/><circle cx="0" cy="5" r="2.5"/><circle cx="48" cy="5" r="2.5"/><circle cx="0" cy="13" r="2.5"/><circle cx="48" cy="13" r="2.5"/><circle cx="0" cy="21" r="2.5"/><circle cx="48" cy="21" r="2.5"/><circle cx="0" cy="29" r="2.5"/><circle cx="48" cy="29" r="2.5"/><circle cx="0" cy="37" r="2.5"/><circle cx="48" cy="37" r="2.5"/><circle cx="0" cy="45" r="2.5"/><circle cx="48" cy="45" r="2.5"/><circle cx="0" cy="53" r="2.5"/><circle cx="48" cy="53" r="2.5"/></g>
  <path d="M13 29H35A11 11 0 1 0 32.4 36.1" fill="none" stroke="#F26B1D" stroke-width="5.2" stroke-linecap="round" stroke-linejoin="round"/>
  <circle cx="40" cy="13" r="8.5" fill="none" stroke="#FFB37A" stroke-width="1.7"/>
  <path d="M51 6q2.75 -2.2 5.5 0t5.5 0t5.5 0t5.5 0" fill="none" stroke="#F26B1D" stroke-width="1.7" stroke-linecap="round"/><path d="M51 11q2.75 -2.2 5.5 0t5.5 0t5.5 0t5.5 0" fill="none" stroke="#F26B1D" stroke-width="1.7" stroke-linecap="round"/><path d="M51 16q2.75 -2.2 5.5 0t5.5 0t5.5 0t5.5 0" fill="none" stroke="#F26B1D" stroke-width="1.7" stroke-linecap="round"/><path d="M51 21q2.75 -2.2 5.5 0t5.5 0t5.5 0t5.5 0" fill="none" stroke="#F26B1D" stroke-width="1.7" stroke-linecap="round"/>
  </g>
  <text x="90" y="42" class="wm"><tspan fill="#F26B1D">e</tspan><tspan fill="#0B1F3A">Filatelia</tspan></text>
  <text x="92" y="57" class="tg" fill="#1E4D8C">leilões de selos em uma só busca</text>
</svg>"""
ICONE_PNG_B64 = "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"

CSS_TEMA = r"""
<style>
@import url('https://fonts.googleapis.com/css2?family=Bricolage+Grotesque:opsz,wght@12..96,600;12..96,700;12..96,800&family=Inter:wght@400;500;600&display=swap');
:root{--navy-900:#0B1F3A;--navy-700:#143A6B;--navy-600:#1E4D8C;--navy-100:#DCE6F5;--navy-50:#F3F7FC;--or-700:#C2410C;--or-600:#D9480F;--or-500:#F26B1D;--or-300:#FFB37A;--or-100:#FFE8D6;--or-50:#FFF6EE;--line:#DCE4EF;--display:'Bricolage Grotesque','Segoe UI',system-ui,sans-serif;--texto:'Inter','Segoe UI',system-ui,sans-serif;}
html,body,.stApp,[data-testid="stAppViewContainer"],[data-testid="stMain"]{background:#FFFFFF !important;color:var(--navy-900);}
.stApp,.stApp p,.stApp label,.stApp li,.stApp input,.stApp textarea,.stApp button,.stApp a,.stApp small,.stApp div[data-baseweb="select"]{font-family:var(--texto);}
.stApp p,.stApp label,.stApp li,.stApp .stMarkdown{color:var(--navy-900);}
header[data-testid="stHeader"]{background:transparent;}
[data-testid="stToolbar"],[data-testid="stDecoration"],#MainMenu,footer{visibility:hidden;}
.block-container{max-width:1100px;padding-top:1.2rem;padding-bottom:4rem;}
.ef-top{display:flex;align-items:center;justify-content:space-between;gap:1rem;flex-wrap:wrap;padding-bottom:1rem;border-bottom:3px dotted var(--or-300);}
.ef-logo svg{height:58px;width:auto;display:block;}
.ef-logo .wm{font-family:var(--display);font-weight:800;font-size:35px;letter-spacing:-.6px;}
.ef-logo .tg{font-family:var(--texto);font-weight:500;font-size:10.5px;letter-spacing:.2px;}
.ef-pill{display:inline-flex;align-items:center;gap:.5rem;background:var(--or-100);color:var(--navy-900);font-weight:600;font-size:.86rem;padding:.4rem .85rem;border-radius:999px;}
.ef-pill i{width:.55rem;height:.55rem;border-radius:50%;background:var(--or-500);display:inline-block;}
.ef-hero{padding:2.2rem 0 1.4rem;}
.stApp .ef-hero .ef-h1{font-family:var(--display);font-weight:800;font-size:clamp(2rem,5vw,3.15rem);line-height:1.04;letter-spacing:-.025em;color:var(--navy-900);margin:0 0 .9rem;}
.stApp .ef-hero p{font-size:1.08rem;line-height:1.55;color:#34507A;max-width:58ch;margin:0;}
.st-key-busca{border:4px dotted var(--or-300);border-radius:16px;background:var(--or-50);padding:1rem 1.1rem 1.1rem;}
.st-key-busca div[data-baseweb="input"]{border:2px solid var(--navy-900);border-radius:10px;background:#fff;min-height:3.1rem;}
.st-key-busca div[data-baseweb="base-input"]{background:#fff;}
.st-key-busca div[data-baseweb="input"] input{font-size:1.08rem;color:var(--navy-900);}
.st-key-busca div[data-baseweb="input"]:focus-within{border-color:var(--or-600);box-shadow:0 0 0 3px var(--or-100);}
.st-key-busca .stButton>button{width:100%;min-height:3.1rem;}
.stApp .ef-hint{margin:.7rem 0 0;font-size:.9rem;color:#5A6F92;}
.stApp button[kind="primary"],.stApp button[data-testid="stBaseButton-primary"],.stApp [data-testid="stFormSubmitButton"]>button{background:var(--or-600);border:0;border-radius:10px;font-weight:700;}
.stApp button[kind="primary"] p,.stApp button[data-testid="stBaseButton-primary"] p,.stApp [data-testid="stFormSubmitButton"]>button p{color:#fff;font-weight:700;}
.stApp button[kind="primary"]:hover,.stApp button[data-testid="stBaseButton-primary"]:hover,.stApp [data-testid="stFormSubmitButton"]>button:hover{background:var(--or-700);}
.stApp button[kind="primary"]:disabled,.stApp button[data-testid="stBaseButton-primary"]:disabled{background:var(--or-600);opacity:.45;}
.stApp button[data-testid="stBaseButton-secondary"],.stApp .stDownloadButton>button{background:#fff;border:2px solid var(--navy-900);border-radius:10px;}
.stApp button[data-testid="stBaseButton-secondary"] p,.stApp .stDownloadButton>button p{color:var(--navy-900);font-weight:600;}
.stApp button:focus-visible{outline:3px solid var(--or-500);outline-offset:2px;}
section[data-testid="stSidebar"]{background:var(--navy-50);border-right:1px solid var(--line);}
section[data-testid="stSidebar"] [data-testid="stExpander"]{background:#fff;border:1px solid var(--line);border-radius:12px;}
.ef-side-title{font-family:var(--display);font-weight:800;font-size:1.3rem;color:var(--navy-900);margin:.1rem 0 .8rem;}
span[data-baseweb="tag"]{background:var(--navy-900) !important;color:#fff !important;}
div[data-testid="stAlert"]{background:var(--or-50);border:1px solid var(--or-300);border-radius:12px;color:var(--navy-900);}
div[data-testid="stProgress"] div[role="progressbar"]>div,.stProgress>div>div>div>div{background-color:var(--or-500) !important;}
.ef-resumo{display:flex;align-items:baseline;gap:.8rem;flex-wrap:wrap;margin:1.6rem 0 .3rem;}
.ef-resumo b{font-family:var(--display);font-weight:800;font-size:2.5rem;line-height:1;color:var(--or-600);}
.ef-resumo span{font-size:1.05rem;color:var(--navy-900);}
.ef-grupo{margin:1.6rem 0 0;}
.ef-grupo-h{display:flex;align-items:center;justify-content:space-between;gap:1rem;padding-bottom:.55rem;border-bottom:2px solid var(--navy-900);}
.ef-grupo-h .ef-h3{font-family:var(--display);font-weight:700;font-size:1.2rem;color:var(--navy-900);}
.ef-badge{background:var(--navy-900);color:#fff;font-weight:600;font-size:.8rem;padding:.2rem .65rem;border-radius:999px;white-space:nowrap;}
.stApp ul.ef-lotes{list-style:none !important;margin:0 !important;padding:0 !important;}
.stApp ul.ef-lotes li{display:flex;align-items:flex-start;justify-content:space-between;gap:1rem;margin:0;padding:.8rem 0;border-bottom:2px dotted var(--or-300);}
.stApp ul.ef-lotes a.t{color:var(--navy-700);font-weight:600;line-height:1.4;text-decoration:none;display:-webkit-box;-webkit-line-clamp:2;-webkit-box-orient:vertical;overflow:hidden;}
.stApp ul.ef-lotes a.t:hover{color:var(--or-600);text-decoration:underline;}
.stApp ul.ef-lotes a.a{flex:none;font-size:.8rem;color:var(--or-700);border:1px solid var(--or-300);border-radius:999px;padding:.15rem .65rem;text-decoration:none;white-space:nowrap;}
.stApp ul.ef-lotes a.a:hover{background:var(--or-100);}
.stApp ul.ef-lotes a:focus-visible{outline:3px solid var(--or-500);outline-offset:2px;border-radius:4px;}
.stApp ul.ef-links{margin:.2rem 0 .8rem;padding-left:1.2rem;}
.stApp ul.ef-links a{color:var(--navy-700);font-weight:500;}
.stApp .ef-sub{font-family:var(--display);font-weight:700;font-size:1rem;margin:1.2rem 0 .2rem;color:var(--navy-900);}
.ef-foot{margin-top:3rem;padding-top:1rem;border-top:3px dotted var(--or-300);color:#5A6F92;font-size:.85rem;}
@media (max-width:640px){.stApp ul.ef-lotes li{flex-direction:column;gap:.4rem;}.ef-logo svg{height:48px;}}
@media (prefers-reduced-motion:reduce){*{transition:none !important;animation:none !important;}}
</style>
"""


def _icone_pagina():
    try:
        from PIL import Image
        return Image.open(io.BytesIO(base64.b64decode(ICONE_PNG_B64)))
    except Exception:
        return "📮"


st.set_page_config(
    page_title="eFilatelia · busca de selos em leilões",
    page_icon=_icone_pagina(),
    layout="wide",
)
st.markdown(CSS_TEMA, unsafe_allow_html=True)
st.markdown(
    '<div class="ef-top"><div class="ef-logo" role="img" aria-label="eFilatelia">'
    + LOGO_SVG
    + '</div><span class="ef-pill"><i></i>Leilões em andamento</span></div>'
    '<div class="ef-hero"><div class="ef-h1" role="heading" aria-level="1">'
    "Todos os leilões de selos<br>em uma só busca</div>"
    "<p>Digite o selo que você procura. O eFilatelia consulta os leilões abertos agora "
    "e mostra cada lote com link direto para o leiloeiro.</p></div>",
    unsafe_allow_html=True,
)

if "sites_v13" not in st.session_state:
    st.session_state.sites_v13 = list(SITES_PADRAO) + carregar_extras()

with st.sidebar:
    st.markdown('<div class="ef-side-title">Sites e filtros</div>', unsafe_allow_html=True)
    nomes = [s.nome for s in st.session_state.sites_v13]
    padrao = [s.nome for s in st.session_state.sites_v13 if s.ativo]

    with st.expander("Sites e limites", expanded=True):
        escolhidos = st.multiselect("Sites a consultar", nomes, default=padrao)
        max_paginas = st.slider("Páginas de resultados por site", 1, 30, 5)
        limite_s = st.slider("Tempo máximo por site (segundos)", 15, 180, 45)

    with st.expander("Filtros", expanded=True):
        exigir_titulo = st.checkbox(
            "Exigir todos os termos no título do lote", value=True,
            help="Ligado (recomendado): descarta lotes cujo título/descrição não contenha todas as "
                 "palavras buscadas. Alguns sites preenchem a lista com itens sem relação.",
        )
        rigor = st.radio(
            "Filtro de selos",
            ["Desligado", "Moderado (recomendado)", "Estrito"],
            index=1,
            help="Moderado: descarta títulos que parecem moeda, cédula, relógio, joia, boneco, "
                 "álbum, livro etc. (a menos que citem selo/filatelia). "
                 "Estrito: só aceita títulos com palavras de selo (selo, RHM, Yvert, Scott, "
                 "bloco, série, carimbo...). Desligado: não filtra.",
        )
        verificar = st.checkbox(
            "Conferir na página do lote se não foi vendido", value=False,
            help="Mais lento: abre cada lote e descarta os marcados como vendido/encerrado.",
        )

    with st.expander("Avançado", expanded=False):
        usar_navegador = st.checkbox(
            "Usar navegador automatizado (Playwright) nos sites com JavaScript", value=False,
            help="Necessário para sites que montam os resultados com JavaScript (ex.: Philasearch, "
                 "Catawiki). Requer: pip install playwright && playwright install chromium. Mais lento.",
        )
        respeitar = st.checkbox("Respeitar robots.txt", value=True)

    with st.expander("Adicionar site", expanded=False):
        st.caption("Abra qualquer site de leilão, faça uma busca por um termo e cole aqui a URL "
                   "da página de resultados. O eFilatelia troca o termo por {q} e a página por {pag}.")
        if st.session_state.get("msg_novo"):
            st.success(st.session_state.pop("msg_novo"))
        with st.form("novo_url", clear_on_submit=True):
            u_nome = st.text_input("Nome do site")
            u_url = st.text_input("URL da página de resultados", placeholder="https://site.com/lots?q=guiana")
            u_termo = st.text_input("Termo que você buscou nessa URL", placeholder="guiana")
            u_js = st.checkbox("Site precisa de JavaScript (Playwright)", value=False)
            if st.form_submit_button("Adicionar site") and u_nome and u_url and u_termo:
                novo, explicacao = site_a_partir_de_url(u_nome, u_url, u_termo, u_js)
                st.session_state.sites_v13 = [
                    x for x in st.session_state.sites_v13 if x.nome != novo.nome
                ] + [novo]
                salvar_extras(st.session_state.sites_v13)
                st.session_state.msg_novo = explicacao
                st.rerun()

        extras_atuais = [x.nome for x in st.session_state.sites_v13 if x.extra]
        if extras_atuais:
            rem = st.selectbox("Remover site adicionado", ["—"] + extras_atuais)
            if rem != "—" and st.button("Remover site"):
                st.session_state.sites_v13 = [x for x in st.session_state.sites_v13 if x.nome != rem]
                salvar_extras(st.session_state.sites_v13)
                st.rerun()

        if st.checkbox("Informar seletor CSS manualmente"):
            with st.form("novo", clear_on_submit=True):
                n_nome = st.text_input("Nome")
                n_url = st.text_input("URL de busca (use {q})", placeholder="https://site.com/busca?q={q}")
                n_sel = st.text_input("Seletor CSS dos links dos lotes", value='a[href*="lote"]')
                n_enc = st.selectbox("Codificação da busca", ["utf-8", "latin-1"])
                n_js = st.checkbox("Site precisa de JavaScript (Playwright)", value=False)
                if st.form_submit_button("Adicionar site") and n_nome and "{q}" in n_url:
                    st.session_state.sites_v13.append(
                        Site(n_nome, n_url, n_sel, n_enc, usa_paginas="{pag}" in n_url,
                             js=n_js, extra=True)
                    )
                    salvar_extras(st.session_state.sites_v13)
                    st.rerun()

# ---- Caixa de busca (moldura pontilhada, como a serrilha de um selo) ----
try:
    caixa = st.container(key="busca")
except TypeError:  # Streamlit antigo, sem 'key' em container
    caixa = st.container()
with caixa:
    col_txt, col_btn = st.columns([5, 1.4])
    with col_txt:
        consulta = st.text_input(
            "Selo buscado",
            placeholder="Ex.: Olho de Boi, Penny Black, RHM B-45",
            label_visibility="collapsed",
        )
    with col_btn:
        buscar = st.button("Buscar selos", type="primary", disabled=not consulta.strip())
st.markdown(
    f'<p class="ef-hint">{len(escolhidos)} sites selecionados. '
    "Ajuste sites e filtros no menu lateral.</p>",
    unsafe_allow_html=True,
)


def executar_busca(sites_sel, consulta_):
    """Consulta os sites em paralelo e devolve (lotes, estatísticas por site)."""
    todos_, stats_ = [], []
    nomes_sel = [s_.nome for s_ in sites_sel]
    barra = st.progress(0.0, text="Consultando: " + ", ".join(nomes_sel)[:200])
    ex = ThreadPoolExecutor(max_workers=max(1, min(8, len(sites_sel))))
    futs = {
        ex.submit(processar_site, s_, consulta_, max_paginas, respeitar,
                  exigir_titulo, verificar, rigor, usar_navegador, limite_s): s_
        for s_ in sites_sel
    }
    pendentes = set(nomes_sel)
    concluidos = 0
    try:
        for f in as_completed(futs, timeout=limite_s + 45):
            s_ = futs[f]
            try:
                res, stt = f.result()
            except Exception as e:  # nenhum site deve derrubar a busca inteira
                res, stt = [], novo_stats(s_.nome)
                stt["Erro"] = f"Erro inesperado: {type(e).__name__}: {e}"
            todos_.extend(res)
            stats_.append(stt)
            pendentes.discard(s_.nome)
            concluidos += 1
            aguardando = ", ".join(sorted(pendentes))[:200] or "nenhum"
            barra.progress(concluidos / len(futs),
                           text=f"{concluidos} de {len(futs)} sites concluídos. Aguardando: {aguardando}")
    except FutTimeout:
        for nome in sorted(pendentes):
            stt = novo_stats(nome)
            stt["Erro"] = "Tempo esgotado: o site não respondeu a tempo (ignorado nesta busca)"
            stats_.append(stt)
    finally:
        ex.shutdown(wait=False, cancel_futures=True)  # não espera threads presas
    barra.empty()
    return todos_, stats_


if buscar:
    sites_escolhidos = [s for s in st.session_state.sites_v13 if s.nome in escolhidos]
    if not sites_escolhidos:
        st.warning("Selecione pelo menos um site no menu lateral.")
    else:
        todos_b, stats_b = executar_busca(sites_escolhidos, consulta.strip())
        # guarda o resultado: clicar em download ou trocar um seletor não apaga a lista
        st.session_state.ultimo = {
            "consulta": consulta.strip(), "todos": todos_b,
            "stats": stats_b, "sites": sites_escolhidos,
        }


def _lista_links(itens, consulta_):
    linhas = []
    for sx, stt in itens:
        url_ = html.escape(url_busca_manual(sx, consulta_), quote=True)
        motivo = f" — <small>{html.escape(stt['Erro'][:110])}</small>" if stt["Erro"] else ""
        linhas.append(f'<li><a href="{url_}" target="_blank" rel="noopener">'
                      f"{html.escape(sx.nome)}</a>{motivo}</li>")
    return '<ul class="ef-links">' + "".join(linhas) + "</ul>"


ultimo = st.session_state.get("ultimo")
if ultimo:
    q = ultimo["consulta"]
    todos, stats_list, sites_sel = ultimo["todos"], ultimo["stats"], ultimo["sites"]

    if todos:
        df = pd.DataFrame(todos).drop_duplicates(subset="Link")
        n = len(df)
        st.markdown(
            f'<div class="ef-resumo"><b>{n}</b><span>{"lote" if n == 1 else "lotes"} em leilões '
            f"em andamento para “{html.escape(q)}”</span></div>",
            unsafe_allow_html=True,
        )
        for nome_site, g in df.groupby("Site", sort=False):
            itens_html = []
            for _, row in g.iterrows():
                t = html.escape(row["Título"])
                # link do portal: idêntico ao que o próprio site usa (mantém os '|')
                a_portal = html.escape(row["Link do portal"], quote=True)
                a_direto = html.escape(row["Link"], quote=True)
                itens_html.append(
                    f'<li><a class="t" href="{a_portal}" target="_blank" rel="noopener">{t}</a>'
                    f'<a class="a" href="{a_direto}" target="_blank" rel="noopener">'
                    "link alternativo</a></li>"
                )
            st.markdown(
                '<div class="ef-grupo"><div class="ef-grupo-h">'
                f'<div class="ef-h3" role="heading" aria-level="2">{html.escape(nome_site)}</div>'
                f'<span class="ef-badge">{len(g)} {"lote" if len(g) == 1 else "lotes"}</span></div>'
                '<ul class="ef-lotes">' + "".join(itens_html) + "</ul></div>",
                unsafe_allow_html=True,
            )
        st.download_button(
            "Baixar resultados (CSV)", df.to_csv(index=False).encode("utf-8-sig"),
            file_name="efilatelia_resultados.csv", mime="text/csv",
        )
    else:
        st.warning(f"Nenhum lote encontrado para “{q}”. O que aconteceu em cada site:")
        for stt in stats_list:
            if stt["Erro"]:
                motivo = stt["Erro"]
            elif stt["Links achados"] == 0:
                motivo = (f"HTTP {stt['HTTP']}, mas nenhum link de lote reconhecido "
                          "(seletor CSS não bate ou a página é montada por JavaScript — "
                          "tente ativar o Playwright em Avançado).")
            else:
                motivo = (f"{stt['Links achados']} link(s) achado(s), todos descartados pelos filtros "
                          f"(título: {stt['Descartados (título)']}, "
                          f"não é selo: {stt['Descartados (não é selo)']}, "
                          f"encerrado: {stt['Descartados (encerrado)']}).")
            st.markdown(f"- **{stt['Site']}**: {motivo}")

    por_nome = {stt["Site"]: stt for stt in stats_list}
    bloqueados = [(sx, por_nome[sx.nome]) for sx in sites_sel
                  if sx.nome in por_nome and por_nome[sx.nome]["Erro"]]
    vazios = [(sx, por_nome[sx.nome]) for sx in sites_sel
              if sx.nome in por_nome and not por_nome[sx.nome]["Erro"]
              and por_nome[sx.nome]["Links achados"] == 0]
    if bloqueados:
        st.markdown('<div class="ef-sub">Sites que o eFilatelia não conseguiu ler. '
                    "Abra a busca direto no navegador:</div>", unsafe_allow_html=True)
        st.markdown(_lista_links(bloqueados, q), unsafe_allow_html=True)
    if vazios:
        st.markdown('<div class="ef-sub">Sites que responderam sem nenhum lote reconhecido '
                    "(pode não haver lotes para o termo, ou a página depende de JavaScript):</div>",
                    unsafe_allow_html=True)
        st.markdown(_lista_links(vazios, q), unsafe_allow_html=True)

    if todos:
        with st.expander("Testar os links (mostra o que o servidor responde)"):
            amostra = pd.DataFrame(todos).drop_duplicates(subset="Link").head(8)
            linhas_teste = []
            for _, row in amostra.iterrows():
                try:
                    r = requests.get(row["Link"], headers=HEADERS, timeout=TIMEOUT)
                    linhas_teste.append({
                        "Título": row["Título"][:60],
                        "HTTP": r.status_code,
                        "URL final": r.url,
                        "Erro do IIS?": "custom error module" in r.text.lower(),
                    })
                except requests.RequestException as e:
                    linhas_teste.append({"Título": row["Título"][:60], "HTTP": "falha",
                                         "URL final": str(e)[:120], "Erro do IIS?": ""})
            st.dataframe(pd.DataFrame(linhas_teste), hide_index=True)

    with st.expander("Diagnóstico por site", expanded=not todos):
        diag_df = pd.DataFrame(stats_list).drop(columns=["_html", "_amostra"])
        st.dataframe(diag_df, hide_index=True)
        st.caption(
            "HTTP diferente de 200 ou Erro preenchido: o site bloqueou ou recusou. "
            "Links achados igual a 0 com HTTP 200: o seletor CSS não bate com o HTML "
            "ou o conteúdo é carregado por JavaScript."
        )
        alvo = st.selectbox("Ver detalhes de um site", [x["Site"] for x in stats_list])
        det = next(x for x in stats_list if x["Site"] == alvo)
        st.code(det["URL"])
        if det["_amostra"]:
            st.markdown("**Exemplos de títulos descartados pelo filtro de título:**")
            st.markdown("\n".join(f"- {t}" for t in det["_amostra"]))
        st.code(det["_html"] or "(vazio)", language="html")

st.markdown(
    '<div class="ef-foot">O eFilatelia reúne resultados de sites de leilão e leva você ao lote '
    "original. Lances e compras acontecem no site do leiloeiro.</div>",
    unsafe_allow_html=True,
)
