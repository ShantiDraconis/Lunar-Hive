"""
Script de transmutação simbólica (anel/colar).
Mantém a lógica documental sem executar operações laboratoriais reais.
Inclui sanitização básica para evitar uso indevido do identificador.
"""

import re

_SAFE_ID_RE = re.compile(r"[^a-zA-Z0-9_-]")


def synthesize(sample_id: str) -> str:
    """Retorna um identificador simbólico de síntese com ID sanitizado."""
    safe_id = _SAFE_ID_RE.sub("_", sample_id)
    if len(safe_id) > 128:
        raise ValueError("sample_id too long for synthesis tag")
    return f"bone-diamond-sim:{safe_id}"


if __name__ == "__main__":
    print(synthesize("prototype-01"))
