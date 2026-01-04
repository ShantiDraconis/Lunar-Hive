#!/usr/bin/env python3
"""
SEO Optimizer - Enhanced for LOG_V97.0
Integrates with metadata_converter.py for comprehensive SEO optimization
"""

from typing import List, Optional

# Core keywords maintained for backward compatibility
KEYWORDS = [
    "Arquitetura de Dados Espaciais",
    "Colonização Lunar",
    "Google Solar Tech",
]

# LOG_V97.0: Enhanced keywords for monetization
MONETIZATION_KEYWORDS = [
    "Shalom Ahavah Tzdek",
    "Data Architecture Monetization",
    "Sustainable Tech Investment",
    "Space Colonization Systems",
    "Advanced Data Structures",
    "Ethical AI Architecture",
    "Solar Technology Integration"
]

# ᚠᚢᚦᛁ 𐏃𐎼𐎱𐎠 — injeta ressonância semântica
# コメント: 保持 frequência ética; nenhuma chave é gravada aqui.

def enrich_title(title: str, extra: Optional[List[str]] = None, enable_monetization_mode: bool = False) -> str:
    """
    Append curated keywords while preserving brevity.
    
    Args:
        title: Base title
        extra: Additional keywords to include
        enable_monetization_mode: Use LOG_V97.0 monetization keywords instead of base keywords
    
    Returns:
        Enhanced title with keywords
    """
    extras = extra or []
    base_keywords = MONETIZATION_KEYWORDS if enable_monetization_mode else KEYWORDS
    bundle = base_keywords + extras
    suffix = " | ".join(bundle[:3])
    return f"{title} — {suffix}" if suffix else title


def build_description(summary: str, depth: int = 1, include_cta: bool = False) -> str:
    """
    Create a description with layered keyword echoes.
    
    Args:
        summary: Base description
        depth: Number of keyword layers
        include_cta: Include call-to-action for monetization
    
    Returns:
        Enhanced description with keywords and optional CTA
    """
    all_keywords = KEYWORDS + MONETIZATION_KEYWORDS
    echoes = " ".join(all_keywords[: min(depth, len(all_keywords))])
    description = f"{summary}\n\n{echoes}"
    
    if include_cta:
        cta = "\n\n📚 Explore more: Amazon Books | 📱 Apple Store | 🔗 GitHub Repository"
        description += cta
    
    return description


def get_high_value_keywords(count: int = 10) -> List[str]:
    """
    Get high-value keywords for advertising auctions.
    
    Args:
        count: Number of keywords to return
    
    Returns:
        List of high-value keywords
    """
    return (KEYWORDS + MONETIZATION_KEYWORDS)[:count]


if __name__ == "__main__":
    import sys

    if len(sys.argv) < 2:
        print("Uso: seo_optimizer.py [title] [--monetization] [--cta]")
        sys.exit(1)
    
    base_title = sys.argv[1]
    enable_monetization_mode = "--monetization" in sys.argv
    include_cta = "--cta" in sys.argv
    
    print("\n=== TÍTULO OTIMIZADO ===")
    print(enrich_title(base_title, enable_monetization_mode=enable_monetization_mode))
    
    print("\n=== DESCRIÇÃO OTIMIZADA ===")
    print(build_description("Sample description", depth=3, include_cta=include_cta))
    
    print("\n=== KEYWORDS DE ALTO VALOR ===")
    for i, kw in enumerate(get_high_value_keywords(5), 1):
        print(f"{i}. {kw}")
    print()
