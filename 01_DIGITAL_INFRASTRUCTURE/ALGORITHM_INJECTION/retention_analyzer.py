#!/usr/bin/env python3
"""
Retention Analyzer - LOG_V97.0 Component
Analyzes video retention to identify "attention nodes" for CTA placement
Target: 1,283.7% retention optimization
"""

from typing import List, Dict, Tuple, Optional
from dataclasses import dataclass
import json


@dataclass
class AttentionNode:
    """Represents a high-retention moment in a video."""
    timestamp: float  # seconds into video
    retention_score: float  # 0.0-1.0
    duration: float  # seconds of sustained attention
    viewer_count: int  # relative viewers at this point
    suggested_cta: str  # recommended call-to-action


@dataclass
class VideoAnalysis:
    """Complete retention analysis for a video."""
    video_id: str
    title: str
    duration: float  # total video length in seconds
    average_retention: float  # overall retention rate
    attention_nodes: List[AttentionNode]
    optimization_score: float  # potential improvement multiplier
    recommended_ctas: List[Tuple[float, str]]  # (timestamp, cta_text)


class RetentionAnalyzer:
    """
    Analyzes video retention patterns to maximize dopamine-driven conversions.
    Identifies optimal moments for CTA insertion based on attention peaks.
    """
    
    # Target optimization multiplier: 1283.7% improvement = 12.837x
    TARGET_OPTIMIZATION_MULTIPLIER = 12.837
    
    # CTA templates optimized for different platforms
    CTA_TEMPLATES = {
        "book_amazon": [
            "📚 Get the full framework in my book on Amazon",
            "🔗 Deep dive available in the eBook - link below",
            "📖 Read the complete analysis on Amazon"
        ],
        "app_apple": [
            "📱 Download the exclusive app on Apple Store",
            "🍎 Get premium content in the iOS app",
            "💎 Unlock full access via Apple Store"
        ],
        "channel_subscribe": [
            "👉 Subscribe for the next part of this series",
            "🔔 Hit subscribe to not miss the continuation",
            "✨ Join the community - subscribe now"
        ],
        "website_visit": [
            "🌐 Full resources at lunarhive.com",
            "🔗 Complete documentation on the website",
            "💻 Explore more at the Lunar Hive repository"
        ]
    }
    
    def __init__(self, data_file: str = "retention_data.json"):
        self.data_file = data_file
        self.analyses: List[VideoAnalysis] = []
        self.load_data()
    
    def load_data(self) -> None:
        """Load retention analysis data from JSON."""
        try:
            with open(self.data_file, 'r') as f:
                data = json.load(f)
                for analysis_data in data.get('analyses', []):
                    # Reconstruct attention nodes
                    nodes = [
                        AttentionNode(**node_data)
                        for node_data in analysis_data.get('attention_nodes', [])
                    ]
                    
                    analysis = VideoAnalysis(
                        video_id=analysis_data['video_id'],
                        title=analysis_data['title'],
                        duration=analysis_data['duration'],
                        average_retention=analysis_data['average_retention'],
                        attention_nodes=nodes,
                        optimization_score=analysis_data['optimization_score'],
                        recommended_ctas=analysis_data.get('recommended_ctas', [])
                    )
                    self.analyses.append(analysis)
        except FileNotFoundError:
            pass
    
    def save_data(self) -> None:
        """Save retention analysis data to JSON."""
        data = {
            'analyses': [
                {
                    'video_id': a.video_id,
                    'title': a.title,
                    'duration': a.duration,
                    'average_retention': a.average_retention,
                    'attention_nodes': [
                        {
                            'timestamp': n.timestamp,
                            'retention_score': n.retention_score,
                            'duration': n.duration,
                            'viewer_count': n.viewer_count,
                            'suggested_cta': n.suggested_cta
                        }
                        for n in a.attention_nodes
                    ],
                    'optimization_score': a.optimization_score,
                    'recommended_ctas': a.recommended_ctas
                }
                for a in self.analyses
            ]
        }
        with open(self.data_file, 'w') as f:
            json.dump(data, f, indent=2)
    
    def analyze_retention_pattern(
        self,
        video_id: str,
        title: str,
        duration: float,
        retention_data: List[Tuple[float, float, int]]
    ) -> VideoAnalysis:
        """
        Analyze retention pattern to identify attention nodes.
        
        Args:
            video_id: Unique video identifier
            title: Video title
            duration: Total video length in seconds
            retention_data: List of (timestamp, retention_rate, viewer_count)
            
        Returns:
            Complete video analysis with attention nodes
        """
        # Calculate average retention
        avg_retention = sum(r[1] for r in retention_data) / len(retention_data)
        
        # Identify attention nodes (peaks in retention)
        attention_nodes = []
        
        for i in range(1, len(retention_data) - 1):
            prev_retention = retention_data[i-1][1]
            curr_retention = retention_data[i][1]
            next_retention = retention_data[i+1][1]
            
            # Look for local maxima with high retention
            if curr_retention > prev_retention and curr_retention > next_retention:
                if curr_retention > avg_retention * 1.2:  # 20% above average
                    # Determine sustained attention duration
                    sustained_duration = self._calculate_sustained_duration(
                        retention_data, i, threshold=avg_retention
                    )
                    
                    # Select appropriate CTA
                    cta = self._select_cta(
                        retention_data[i][0],
                        curr_retention,
                        sustained_duration
                    )
                    
                    node = AttentionNode(
                        timestamp=retention_data[i][0],
                        retention_score=curr_retention,
                        duration=sustained_duration,
                        viewer_count=retention_data[i][2],
                        suggested_cta=cta
                    )
                    attention_nodes.append(node)
        
        # Sort nodes by retention score
        attention_nodes.sort(key=lambda n: n.retention_score, reverse=True)
        
        # Calculate optimization score (potential improvement)
        if avg_retention > 0:
            # Target: 1283.7% optimization (12.837x multiplier)
            optimization_score = (1.0 - avg_retention) * self.TARGET_OPTIMIZATION_MULTIPLIER
        else:
            optimization_score = self.TARGET_OPTIMIZATION_MULTIPLIER
        
        # Generate recommended CTAs
        recommended_ctas = self._generate_cta_recommendations(attention_nodes)
        
        analysis = VideoAnalysis(
            video_id=video_id,
            title=title,
            duration=duration,
            average_retention=avg_retention,
            attention_nodes=attention_nodes[:10],  # Keep top 10 nodes
            optimization_score=optimization_score,
            recommended_ctas=recommended_ctas
        )
        
        self.analyses.append(analysis)
        self.save_data()
        
        return analysis
    
    def _calculate_sustained_duration(
        self,
        retention_data: List[Tuple[float, float, int]],
        peak_index: int,
        threshold: float
    ) -> float:
        """Calculate how long retention stays above threshold around peak."""
        duration = 0.0
        
        # Look forward
        for i in range(peak_index, len(retention_data)):
            if retention_data[i][1] < threshold:
                break
            if i < len(retention_data) - 1:
                duration += retention_data[i+1][0] - retention_data[i][0]
        
        # Look backward
        for i in range(peak_index, 0, -1):
            if retention_data[i][1] < threshold:
                break
            if i > 0:
                duration += retention_data[i][0] - retention_data[i-1][0]
        
        return max(duration, 1.0)  # Minimum 1 second
    
    def _select_cta(
        self,
        timestamp: float,
        retention_score: float,
        duration: float
    ) -> str:
        """Select the most appropriate CTA for this attention node."""
        # Very high retention + long duration = prime for book/app CTA
        if retention_score > 0.8 and duration > 10:
            if timestamp < 180:  # First 3 minutes
                return self.CTA_TEMPLATES["channel_subscribe"][0]
            else:
                return self.CTA_TEMPLATES["book_amazon"][0]
        
        # Medium retention = subscribe CTA
        elif retention_score > 0.6:
            return self.CTA_TEMPLATES["channel_subscribe"][1]
        
        # Early in video = website visit
        elif timestamp < 120:
            return self.CTA_TEMPLATES["website_visit"][0]
        
        # Default to book promotion
        else:
            return self.CTA_TEMPLATES["book_amazon"][1]
    
    def _generate_cta_recommendations(
        self,
        attention_nodes: List[AttentionNode]
    ) -> List[Tuple[float, str]]:
        """Generate final CTA placement recommendations."""
        recommendations = []
        
        # Take top 3 attention nodes
        for node in attention_nodes[:3]:
            recommendations.append((node.timestamp, node.suggested_cta))
        
        return recommendations
    
    def get_optimization_report(self, video_id: str) -> str:
        """Generate optimization report for a specific video."""
        analysis = None
        for a in self.analyses:
            if a.video_id == video_id:
                analysis = a
                break
        
        if not analysis:
            return f"Nenhuma análise encontrada para video_id: {video_id}"
        
        report = f"""
========================================
RETENTION ANALYSIS - {analysis.title}
========================================
Video ID: {analysis.video_id}
Duração: {analysis.duration:.0f}s ({analysis.duration/60:.1f} min)
Retenção Média: {analysis.average_retention*100:.1f}%
Score de Otimização: {analysis.optimization_score:.2f}x

NÓS DE ATENÇÃO IDENTIFICADOS:
"""
        
        for i, node in enumerate(analysis.attention_nodes[:5], 1):
            timestamp_str = f"{int(node.timestamp//60)}:{int(node.timestamp%60):02d}"
            report += f"\n{i}. @ {timestamp_str} - Retenção: {node.retention_score*100:.1f}%\n"
            report += f"   Duração sustentada: {node.duration:.1f}s\n"
            report += f"   CTA sugerido: {node.suggested_cta}\n"
        
        report += "\n\nCTAs RECOMENDADOS:\n"
        for timestamp, cta in analysis.recommended_ctas:
            timestamp_str = f"{int(timestamp//60)}:{int(timestamp%60):02d}"
            report += f"\n⏱️  {timestamp_str} - {cta}\n"
        
        report += f"""
========================================
POTENCIAL DE MELHORIA:
Com otimização adequada de CTAs nos nós de atenção,
espera-se aumento de conversão de até {analysis.optimization_score*100:.1f}%
========================================
"""
        return report
    
    def get_channel_summary(self) -> str:
        """Generate summary report for all analyzed videos."""
        if not self.analyses:
            return "Nenhuma análise disponível ainda."
        
        total_videos = len(self.analyses)
        avg_retention = sum(a.average_retention for a in self.analyses) / total_videos
        avg_optimization = sum(a.optimization_score for a in self.analyses) / total_videos
        
        report = f"""
========================================
RESUMO DO CANAL - ANÁLISE DE RETENÇÃO
========================================
Total de vídeos analisados: {total_videos}
Retenção média do canal: {avg_retention*100:.1f}%
Potencial de otimização médio: {avg_optimization:.2f}x

TOP 5 VÍDEOS POR RETENÇÃO:
"""
        
        top_videos = sorted(
            self.analyses,
            key=lambda a: a.average_retention,
            reverse=True
        )[:5]
        
        for i, video in enumerate(top_videos, 1):
            report += f"\n{i}. {video.title[:50]}"
            report += f"\n   Retenção: {video.average_retention*100:.1f}%"
            report += f"\n   Nós de atenção: {len(video.attention_nodes)}\n"
        
        report += """
========================================
META: Alcançar 1.283,7% de otimização através
de CTAs estrategicamente posicionados nos
momentos de dopamina máxima.
========================================
"""
        return report


def main():
    """CLI interface for retention analyzer."""
    import sys
    
    analyzer = RetentionAnalyzer()
    
    if len(sys.argv) < 2:
        print("Uso: retention_analyzer.py [report|summary|analyze]")
        sys.exit(1)
    
    command = sys.argv[1]
    
    if command == "report":
        if len(sys.argv) < 3:
            print("Uso: report [video_id]")
            sys.exit(1)
        
        video_id = sys.argv[2]
        print(analyzer.get_optimization_report(video_id))
        
    elif command == "summary":
        print(analyzer.get_channel_summary())
        
    elif command == "analyze":
        # Example placeholder
        print("Análise de retenção requer dados do YouTube Analytics")
        print("Integrar com YouTube Data API para análise real")
        
    else:
        print(f"Comando desconhecido: {command}")


if __name__ == "__main__":
    main()
