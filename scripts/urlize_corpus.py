"""Regenerate tests/golden/urlize_unicode.json: 6000 Unicode-heavy words and
jinja2's urlize output for each, for the differential case in
tests/Conformance.lean. Run with: upstream-spec/.venv/bin/python -I scripts/urlize_corpus.py
"""
import random, json, jinja2
random.seed(2026)
env = jinja2.Environment()
uni = ["²", "½", "·", "́", "é", "ß", "٣", "１", "Ⅷ", "ſ", "K", "ı", "İ", " ", " ", "　", "\u0085", " ", "​", "中", "😀", "_", "ª", "º", "µ", "٣", " ", "\u001c", "‐", "–"]
pieces = ["http://", "https://", "www.", "mailto:", "ex", ".com", ".org", ".io", ".xn--", "@", "a", "b", ".", ",", "(", ")", "<", ">", ":", "80", "/p", "?q", "#f", "[::1]", "127.0.0.1", "-", "%"]
def rc():
    while True:
        cp = random.randrange(0x80, 0x30000)
        if not 0xD800 <= cp <= 0xDFFF: return chr(cp)
out = []
src = "{{ x|urlize }}"
while len(out) < 6000:
    n = random.randint(2, 8)
    parts = []
    for _ in range(n):
        k = random.random()
        parts.append(random.choice(uni) if k < 0.35 else rc() if k < 0.45 else random.choice(pieces))
    t = "".join(parts)
    if all(ord(c) < 128 for c in t): continue
    out.append({"src": src, "x": t, "out": env.from_string(src).render(x=t)})
import pathlib
OUT = pathlib.Path(__file__).resolve().parents[1] / "tests/golden/urlize_unicode.json"
json.dump(out, open(OUT, "w"), ensure_ascii=False); print(len(out), "words ->", OUT)
