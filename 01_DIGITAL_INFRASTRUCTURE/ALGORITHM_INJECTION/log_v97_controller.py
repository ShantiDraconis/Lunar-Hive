#!/usr/bin/env python3
"""
LOG_V97.0 Master Controller
Coordinates all components of the financial traction mechanism
"""

import sys
import os
from datetime import datetime

# Add the current directory to path for imports
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

try:
    from financial_flow_tracker import FinancialFlowTracker
    from metadata_converter import MetadataConverter
    from retention_analyzer import RetentionAnalyzer
    from revenue_allocator import RevenueAllocator
    import seo_optimizer
except ImportError as e:
    print(f"⚠️  Warning: Could not import all components: {e}")
    print("Some features may be limited.")


class LOG_V97_Controller:
    """Master controller for the LOG_V97.0 financial traction system."""
    
    def __init__(self):
        self.financial_tracker = FinancialFlowTracker()
        self.metadata_converter = MetadataConverter()
        self.retention_analyzer = RetentionAnalyzer()
        self.revenue_allocator = RevenueAllocator()
    
    def dashboard(self) -> str:
        """Generate a comprehensive dashboard of all systems."""
        
        # Get financial status
        totals = self.financial_tracker.calculate_totals()
        
        # Get allocation status
        milestone = self.revenue_allocator.get_next_naval_milestone()
        
        dashboard = f"""
╔══════════════════════════════════════════════════════════════════════╗
║                  LOG_V97.0 - SISTEMA DE CONTROLE                     ║
║          MECANISMO DE TRAÇÃO E FLUXO FINANCEIRO                      ║
╚══════════════════════════════════════════════════════════════════════╝

📅 Data: {datetime.now().strftime('%d/%m/%Y %H:%M:%S')}

┌─────────────────────────────────────────────────────────────────────┐
│ 💰 RECEITAS POR PLATAFORMA                                          │
├─────────────────────────────────────────────────────────────────────┤
│  Amazon (Royalties):    ${totals['amazon']:>10,.2f}                │
│  Apple (Apps/Mídia):    ${totals['apple']:>10,.2f}                 │
│  YouTube (AdSense):     ${totals['youtube']:>10,.2f}               │
│  ─────────────────────────────────────────                         │
│  TOTAL:                 ${totals['total']:>10,.2f}                 │
└─────────────────────────────────────────────────────────────────────┘

┌─────────────────────────────────────────────────────────────────────┐
│ 📊 ALOCAÇÃO DE RECURSOS                                             │
├─────────────────────────────────────────────────────────────────────┤
│  Capital de Giro (30%): ${self.revenue_allocator.totals['capital_giro']:>10,.2f}│
│  Fundo Naval (50%):     ${self.revenue_allocator.totals['fundo_naval']:>10,.2f}│
│  Fundo Tera (20%):      ${self.revenue_allocator.totals['fundo_tera']:>10,.2f} │
└─────────────────────────────────────────────────────────────────────┘

┌─────────────────────────────────────────────────────────────────────┐
│ 🎯 METAS E PROGRESSO                                                │
├─────────────────────────────────────────────────────────────────────┤
│  Meta Fevereiro/2026:   $7,000.00                                  │
│  Progresso:             {(totals['total'] / 7000.0 * 100):>6.1f}%  │
│                                                                     │
│  Meta Barco Escola:     $12,000.00/mês (a partir de Março)        │
│  Fundo Naval Atual:     ${milestone['current']:>10,.2f}           │
│  Próxima Meta:          ${milestone['target']:>10,.2f}            │
│  {milestone['description']:<60}│
│  Progresso:             {milestone['progress']:>6.1f}%            │
└─────────────────────────────────────────────────────────────────────┘

┌─────────────────────────────────────────────────────────────────────┐
│ 🔍 OTIMIZAÇÃO DE METADADOS                                          │
├─────────────────────────────────────────────────────────────────────┤
│  Ativos convertidos:    {len(self.metadata_converter.assets)}      │
│  Keywords de alto valor: Disponíveis para 3 plataformas           │
│  Status SEO:            ✅ Ativo                                    │
└─────────────────────────────────────────────────────────────────────┘

┌─────────────────────────────────────────────────────────────────────┐
│ 📈 ANÁLISE DE RETENÇÃO                                              │
├─────────────────────────────────────────────────────────────────────┤
│  Vídeos analisados:     {len(self.retention_analyzer.analyses)}    │
│  Meta de otimização:    1.283,7% (12.837x)                        │
│  Status:                {'✅ Ativo' if len(self.retention_analyzer.analyses) > 0 else '⏳ Aguardando dados'}│
└─────────────────────────────────────────────────────────────────────┘

┌─────────────────────────────────────────────────────────────────────┐
│ ⚡ AÇÕES RÁPIDAS                                                     │
├─────────────────────────────────────────────────────────────────────┤
│  1. Adicionar receita:     ./log_v97_controller.py add-revenue     │
│  2. Ver relatório completo: ./log_v97_controller.py full-report    │
│  3. Otimizar título:       ./log_v97_controller.py optimize-title  │
│  4. Status de milestone:   ./log_v97_controller.py milestone       │
└─────────────────────────────────────────────────────────────────────┘

╔══════════════════════════════════════════════════════════════════════╗
║ Sistema operacional e pronto para monetização                        ║
║ Documentação: LOG_V97_0_FINANCIAL_TRACTION.md                        ║
╚══════════════════════════════════════════════════════════════════════╝
"""
        return dashboard
    
    def add_revenue_interactive(self):
        """Interactive revenue addition."""
        print("\n=== ADICIONAR RECEITA ===\n")
        
        print("Plataforma:")
        print("  1. Amazon")
        print("  2. Apple")
        print("  3. YouTube")
        
        platform_choice = input("\nEscolha (1-3): ").strip()
        platform_map = {"1": "amazon", "2": "apple", "3": "youtube"}
        platform = platform_map.get(platform_choice, "amazon")
        
        amount = float(input("Valor ($): "))
        
        print("\nTipo de receita:")
        print("  1. Royalty (Amazon)")
        print("  2. App Sale (Apple)")
        print("  3. AdSense (YouTube)")
        print("  4. Consulting")
        
        type_choice = input("\nEscolha (1-4): ").strip()
        type_map = {"1": "royalty", "2": "app_sale", "3": "adsense", "4": "consulting"}
        source_type = type_map.get(type_choice, "royalty")
        
        # Add revenue to tracker
        self.financial_tracker.add_revenue(platform, amount, source_type)
        
        # Allocate revenue
        allocation = self.revenue_allocator.allocate_revenue(amount)
        
        print(f"\n✅ Receita adicionada: ${amount:,.2f}")
        print(f"\nAlocação automática:")
        print(f"  Capital de Giro: ${allocation.capital_giro:,.2f}")
        print(f"  Fundo Naval:     ${allocation.fundo_naval:,.2f}")
        print(f"  Fundo Tera:      ${allocation.fundo_tera:,.2f}")
        print()
    
    def optimize_title_interactive(self):
        """Interactive title optimization."""
        print("\n=== OTIMIZAR TÍTULO ===\n")
        
        title = input("Título base: ")
        
        print("\nPlataforma alvo:")
        print("  1. YouTube")
        print("  2. Amazon")
        print("  3. Apple")
        
        platform_choice = input("\nEscolha (1-3): ").strip()
        platform_map = {"1": "youtube", "2": "amazon", "3": "apple"}
        platform = platform_map.get(platform_choice, "youtube")
        
        optimized = self.metadata_converter.generate_title_optimization(title, platform)
        
        print(f"\n✨ Título otimizado:\n{optimized}\n")
    
    def full_report(self) -> str:
        """Generate a comprehensive report of all systems."""
        report = f"""
{'='*80}
LOG_V97.0 - RELATÓRIO COMPLETO DO SISTEMA
{'='*80}
Data: {datetime.now().strftime('%d/%m/%Y %H:%M:%S')}

"""
        report += self.financial_tracker.get_status_report()
        report += "\n"
        report += self.revenue_allocator.get_allocation_summary()
        report += "\n"
        report += self.metadata_converter.generate_seo_report()
        
        if len(self.retention_analyzer.analyses) > 0:
            report += "\n"
            report += self.retention_analyzer.get_channel_summary()
        
        return report


def main():
    """CLI interface for LOG_V97.0 controller."""
    
    controller = LOG_V97_Controller()
    
    if len(sys.argv) < 2:
        print(controller.dashboard())
        return
    
    command = sys.argv[1]
    
    if command == "dashboard":
        print(controller.dashboard())
        
    elif command == "add-revenue":
        controller.add_revenue_interactive()
        
    elif command == "optimize-title":
        controller.optimize_title_interactive()
        
    elif command == "milestone":
        milestone = controller.revenue_allocator.get_next_naval_milestone()
        print(f"\n🎯 Próxima Meta do Fundo Naval")
        print(f"   Valor: ${milestone['target']:,.2f}")
        print(f"   Descrição: {milestone['description']}")
        print(f"   Atual: ${milestone['current']:,.2f}")
        print(f"   Progresso: {milestone['progress']:.1f}%")
        print(f"   Faltam: ${milestone['remaining']:,.2f}\n")
        
    elif command == "full-report":
        print(controller.full_report())
        
    elif command == "help":
        print("""
LOG_V97.0 - Sistema de Controle de Fluxo Financeiro

Comandos disponíveis:
  dashboard        - Mostrar dashboard principal (padrão)
  add-revenue      - Adicionar receita interativamente
  optimize-title   - Otimizar título para plataforma
  milestone        - Mostrar próxima meta do Fundo Naval
  full-report      - Gerar relatório completo
  help             - Mostrar esta ajuda

Componentes individuais:
  financial_flow_tracker.py - Rastreamento de receitas
  metadata_converter.py     - Conversão de metadados
  retention_analyzer.py     - Análise de retenção
  revenue_allocator.py      - Alocação de recursos
  seo_optimizer.py          - Otimização SEO

Documentação completa: LOG_V97_0_FINANCIAL_TRACTION.md
""")
        
    else:
        print(f"Comando desconhecido: {command}")
        print("Use 'help' para ver comandos disponíveis")


if __name__ == "__main__":
    main()
