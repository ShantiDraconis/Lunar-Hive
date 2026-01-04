#!/usr/bin/env python3
"""
Metadata Converter - LOG_V97.0 Component
Converts Data Architecture (I = 0/0) into monetizable metadata
"""

from typing import List, Dict, Optional
from dataclasses import dataclass


@dataclass
class MetadataAsset:
    """Represents a piece of converted metadata."""
    concept: str
    keywords: List[str]
    target_platforms: List[str]
    value_score: float  # 0.0-1.0, estimated monetization potential
    category: str


class MetadataConverter:
    """
    Converts Shalom Ahavah Tzdek concepts and Data Architecture 
    into high-value keywords for advertising auctions.
    """
    
    # Maximum number of platform-specific modifiers to add per keyword
    MAX_MODIFIERS_PER_KEYWORD = 2
    
    # Core concepts from Lunar Hive architecture
    CORE_CONCEPTS = {
        "I = 0/0": {
            "keywords": [
                "Indeterminate Forms",
                "Mathematical Limits",
                "Zero Division Architecture",
                "Advanced Mathematics",
                "Computational Theory"
            ],
            "category": "mathematical",
            "value_score": 0.85
        },
        "Shalom Ahavah Tzdek": {
            "keywords": [
                "Ethical Data Systems",
                "Peace Technology",
                "Love-Based Architecture",
                "Justice in AI",
                "Sustainable Tech Ethics"
            ],
            "category": "ethical",
            "value_score": 0.90
        },
        "Lunar Colonization": {
            "keywords": [
                "Space Architecture",
                "Lunar Hive Systems",
                "Moon Colony Planning",
                "Space Sustainability",
                "Extraterrestrial Data Systems"
            ],
            "category": "space",
            "value_score": 0.95
        },
        "Data Sovereignty": {
            "keywords": [
                "Data Architecture Authority",
                "Digital Sovereignty",
                "Decentralized Systems",
                "Privacy-First Tech",
                "Self-Sovereign Data"
            ],
            "category": "sovereignty",
            "value_score": 0.88
        },
        "Harappan Script": {
            "keywords": [
                "Ancient Cryptography",
                "Indus Valley Technology",
                "Historical Data Systems",
                "Archaeological Computing",
                "Proto-Writing Analysis"
            ],
            "category": "historical",
            "value_score": 0.75
        },
        "Biotech Legacy": {
            "keywords": [
                "DNA Data Storage",
                "Biological Computing",
                "Carbon Synthesis",
                "Bio-Encryption",
                "Legacy Preservation Tech"
            ],
            "category": "biotech",
            "value_score": 0.92
        }
    }
    
    # Platform-specific keyword optimization
    PLATFORM_MODIFIERS = {
        "amazon": ["Book", "eBook", "Read", "Learn", "Guide"],
        "apple": ["App", "iOS", "macOS", "Digital", "Premium"],
        "youtube": ["Tutorial", "Explained", "Documentary", "Series", "Course"]
    }
    
    def __init__(self):
        self.assets: List[MetadataAsset] = []
        self._generate_base_assets()
    
    def _generate_base_assets(self) -> None:
        """Generate metadata assets from core concepts."""
        for concept, data in self.CORE_CONCEPTS.items():
            asset = MetadataAsset(
                concept=concept,
                keywords=data["keywords"],
                target_platforms=["amazon", "apple", "youtube"],
                value_score=data["value_score"],
                category=data["category"]
            )
            self.assets.append(asset)
    
    def get_keywords_for_platform(
        self,
        platform: str,
        category: Optional[str] = None,
        top_n: int = 10
    ) -> List[str]:
        """
        Get optimized keywords for a specific platform.
        
        Args:
            platform: "amazon", "apple", or "youtube"
            category: Optional filter by category
            top_n: Number of keywords to return
            
        Returns:
            List of optimized keywords
        """
        # Filter assets
        filtered_assets = self.assets
        if category:
            filtered_assets = [a for a in filtered_assets if a.category == category]
        
        # Sort by value score
        filtered_assets.sort(key=lambda a: a.value_score, reverse=True)
        
        # Collect keywords
        keywords = []
        modifiers = self.PLATFORM_MODIFIERS.get(platform, [])
        
        for asset in filtered_assets:
            for keyword in asset.keywords:
                keywords.append(keyword)
                # Add platform-specific variations
                for modifier in modifiers[:self.MAX_MODIFIERS_PER_KEYWORD]:
                    keywords.append(f"{keyword} {modifier}")
        
        # Return top N unique keywords
        unique_keywords = []
        seen = set()
        for kw in keywords:
            if kw.lower() not in seen:
                unique_keywords.append(kw)
                seen.add(kw.lower())
                if len(unique_keywords) >= top_n:
                    break
        
        return unique_keywords
    
    def generate_title_optimization(
        self,
        base_title: str,
        platform: str = "youtube"
    ) -> str:
        """
        Optimize a title with high-value keywords.
        
        Args:
            base_title: Original title
            platform: Target platform
            
        Returns:
            Optimized title with keywords
        """
        # Get top 2 keywords for the platform
        keywords = self.get_keywords_for_platform(platform, top_n=2)
        
        # Create optimized title
        keyword_suffix = " | ".join(keywords[:2])
        optimized = f"{base_title} — {keyword_suffix}"
        
        return optimized
    
    def generate_description(
        self,
        summary: str,
        platform: str = "youtube",
        depth: int = 5
    ) -> str:
        """
        Generate an SEO-optimized description.
        
        Args:
            summary: Base summary/description
            platform: Target platform
            depth: Number of keyword echoes to include
            
        Returns:
            Optimized description
        """
        keywords = self.get_keywords_for_platform(platform, top_n=depth)
        keyword_section = "\n\n🔑 Keywords: " + ", ".join(keywords)
        
        description = f"{summary}{keyword_section}"
        
        # Add call-to-action based on platform
        if platform == "amazon":
            cta = "\n\n📚 Available now in eBook and paperback formats."
        elif platform == "apple":
            cta = "\n\n📱 Download the app for exclusive content and features."
        elif platform == "youtube":
            cta = "\n\n👉 Subscribe for more content on space technology and data architecture."
        else:
            cta = ""
        
        return description + cta
    
    def get_auction_keywords(
        self,
        budget_tier: str = "premium"
    ) -> Dict[str, List[str]]:
        """
        Get keywords optimized for advertising auctions.
        
        Args:
            budget_tier: "premium", "mid", or "low"
            
        Returns:
            Dictionary of keywords by category with bid recommendations
        """
        # Premium tier targets high-value, low-competition keywords
        if budget_tier == "premium":
            min_score = 0.85
        elif budget_tier == "mid":
            min_score = 0.75
        else:
            min_score = 0.60
        
        result = {}
        for asset in self.assets:
            if asset.value_score >= min_score:
                if asset.category not in result:
                    result[asset.category] = []
                result[asset.category].extend(asset.keywords[:3])
        
        return result
    
    def generate_seo_report(self) -> str:
        """Generate a comprehensive SEO optimization report."""
        report = """
========================================
LOG_V97.0 - METADATA CONVERSION REPORT
========================================

ATIVOS DE METADADOS CONVERTIDOS:
"""
        
        for asset in sorted(self.assets, key=lambda a: a.value_score, reverse=True):
            report += f"\n📊 {asset.concept} (Score: {asset.value_score:.2f})\n"
            report += f"   Categoria: {asset.category}\n"
            report += f"   Keywords: {', '.join(asset.keywords[:3])}\n"
        
        report += "\n\nPALAVRAS-CHAVE DE ALTO VALOR:\n"
        
        for platform in ["amazon", "apple", "youtube"]:
            keywords = self.get_keywords_for_platform(platform, top_n=5)
            report += f"\n{platform.upper()}:\n"
            for i, kw in enumerate(keywords, 1):
                report += f"  {i}. {kw}\n"
        
        report += """
========================================
RECOMENDAÇÕES:
1. Use estas keywords em títulos e descrições
2. Priorize keywords com score > 0.85
3. Ajuste baseado em performance de conversão
========================================
"""
        return report


def main():
    """CLI interface for metadata converter."""
    import sys
    
    converter = MetadataConverter()
    
    if len(sys.argv) < 2:
        print("Uso: metadata_converter.py [report|keywords|title|description]")
        sys.exit(1)
    
    command = sys.argv[1]
    
    if command == "report":
        print(converter.generate_seo_report())
        
    elif command == "keywords":
        # keywords [platform] [n]
        platform = sys.argv[2] if len(sys.argv) > 2 else "youtube"
        n = int(sys.argv[3]) if len(sys.argv) > 3 else 10
        
        keywords = converter.get_keywords_for_platform(platform, top_n=n)
        print(f"\nTop {n} keywords para {platform}:")
        for i, kw in enumerate(keywords, 1):
            print(f"  {i}. {kw}")
        print()
        
    elif command == "title":
        # title [base_title] [platform]
        if len(sys.argv) < 3:
            print("Uso: title [base_title] [platform]")
            sys.exit(1)
        
        base_title = sys.argv[2]
        platform = sys.argv[3] if len(sys.argv) > 3 else "youtube"
        
        optimized = converter.generate_title_optimization(base_title, platform)
        print(f"\nTítulo otimizado:\n{optimized}\n")
        
    elif command == "description":
        # description [summary] [platform]
        if len(sys.argv) < 3:
            print("Uso: description [summary] [platform]")
            sys.exit(1)
        
        summary = sys.argv[2]
        platform = sys.argv[3] if len(sys.argv) > 3 else "youtube"
        
        desc = converter.generate_description(summary, platform)
        print(f"\nDescrição otimizada:\n{desc}\n")
        
    else:
        print(f"Comando desconhecido: {command}")


if __name__ == "__main__":
    main()
