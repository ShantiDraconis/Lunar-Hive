#!/usr/bin/env python3
"""
Financial Flow Tracker - LOG_V97.0 Component
Tracks revenue streams from Amazon, Apple Store, and Google/YouTube
"""

from datetime import datetime
from typing import Dict, List, Optional
from dataclasses import dataclass, field
import json


@dataclass
class RevenueStream:
    """Represents a single revenue stream from a platform."""
    platform: str  # "amazon", "apple", "youtube"
    amount: float
    date: str
    source_type: str  # "royalty", "adsense", "app_sale", "consulting"
    metadata: Dict = field(default_factory=dict)


@dataclass
class FinancialSnapshot:
    """Snapshot of financial status at a point in time."""
    date: str
    total_revenue: float
    amazon_revenue: float
    apple_revenue: float
    youtube_revenue: float
    capital_giro: float  # Working capital (30%)
    fundo_naval: float   # Naval fund (50%)
    fundo_tera: float    # Tera fund (20%)


class FinancialFlowTracker:
    """
    Main tracker for LOG_V97.0 financial flows.
    Manages revenue tracking and allocation across three funds.
    """
    
    def __init__(self, data_file: str = "financial_data.json"):
        self.data_file = data_file
        self.revenue_streams: List[RevenueStream] = []
        self.snapshots: List[FinancialSnapshot] = []
        self.load_data()
    
    def load_data(self) -> None:
        """Load existing financial data from JSON file."""
        try:
            with open(self.data_file, 'r') as f:
                data = json.load(f)
                # Load revenue streams
                for stream_data in data.get('revenue_streams', []):
                    self.revenue_streams.append(
                        RevenueStream(**stream_data)
                    )
                # Load snapshots
                for snapshot_data in data.get('snapshots', []):
                    self.snapshots.append(
                        FinancialSnapshot(**snapshot_data)
                    )
        except FileNotFoundError:
            # First run, no data yet
            pass
    
    def save_data(self) -> None:
        """Save financial data to JSON file."""
        data = {
            'revenue_streams': [
                {
                    'platform': s.platform,
                    'amount': s.amount,
                    'date': s.date,
                    'source_type': s.source_type,
                    'metadata': s.metadata
                }
                for s in self.revenue_streams
            ],
            'snapshots': [
                {
                    'date': s.date,
                    'total_revenue': s.total_revenue,
                    'amazon_revenue': s.amazon_revenue,
                    'apple_revenue': s.apple_revenue,
                    'youtube_revenue': s.youtube_revenue,
                    'capital_giro': s.capital_giro,
                    'fundo_naval': s.fundo_naval,
                    'fundo_tera': s.fundo_tera
                }
                for s in self.snapshots
            ]
        }
        with open(self.data_file, 'w') as f:
            json.dump(data, f, indent=2)
    
    def add_revenue(
        self,
        platform: str,
        amount: float,
        source_type: str,
        metadata: Optional[Dict] = None
    ) -> None:
        """Add a new revenue entry."""
        stream = RevenueStream(
            platform=platform,
            amount=amount,
            date=datetime.now().isoformat(),
            source_type=source_type,
            metadata=metadata or {}
        )
        self.revenue_streams.append(stream)
        self.save_data()
    
    def calculate_totals(self) -> Dict[str, float]:
        """Calculate total revenue by platform."""
        totals = {
            'total': 0.0,
            'amazon': 0.0,
            'apple': 0.0,
            'youtube': 0.0
        }
        
        for stream in self.revenue_streams:
            totals['total'] += stream.amount
            if stream.platform == 'amazon':
                totals['amazon'] += stream.amount
            elif stream.platform == 'apple':
                totals['apple'] += stream.amount
            elif stream.platform == 'youtube':
                totals['youtube'] += stream.amount
        
        return totals
    
    def allocate_funds(self, total_revenue: float) -> Dict[str, float]:
        """
        Allocate funds according to LOG_V97.0 distribution:
        - 30% Capital de Giro (Working Capital)
        - 50% Fundo Naval (Naval Fund)
        - 20% Fundo Tera (Tera Fund)
        """
        return {
            'capital_giro': total_revenue * 0.30,
            'fundo_naval': total_revenue * 0.50,
            'fundo_tera': total_revenue * 0.20
        }
    
    def create_snapshot(self) -> FinancialSnapshot:
        """Create a financial snapshot for the current state."""
        totals = self.calculate_totals()
        allocation = self.allocate_funds(totals['total'])
        
        snapshot = FinancialSnapshot(
            date=datetime.now().isoformat(),
            total_revenue=totals['total'],
            amazon_revenue=totals['amazon'],
            apple_revenue=totals['apple'],
            youtube_revenue=totals['youtube'],
            capital_giro=allocation['capital_giro'],
            fundo_naval=allocation['fundo_naval'],
            fundo_tera=allocation['fundo_tera']
        )
        
        self.snapshots.append(snapshot)
        self.save_data()
        return snapshot
    
    def get_status_report(self) -> str:
        """Generate a human-readable status report."""
        totals = self.calculate_totals()
        allocation = self.allocate_funds(totals['total'])
        
        report = f"""
========================================
LOG_V97.0 - FINANCIAL FLOW TRACKER
========================================
Data: {datetime.now().strftime('%d/%m/%Y %H:%M')}

RECEITAS POR PLATAFORMA:
  Amazon:     ${totals['amazon']:,.2f}
  Apple:      ${totals['apple']:,.2f}
  YouTube:    ${totals['youtube']:,.2f}
  ─────────────────────────────
  TOTAL:      ${totals['total']:,.2f}

ALOCAÇÃO DE RECURSOS:
  Capital de Giro (30%): ${allocation['capital_giro']:,.2f}
  Fundo Naval (50%):     ${allocation['fundo_naval']:,.2f}
  Fundo Tera (20%):      ${allocation['fundo_tera']:,.2f}

META FEVEREIRO: $7,000.00
Progresso: {(totals['total'] / 7000.0 * 100):.1f}%

META MARÇO (Barco Escola): $12,000.00/mês
Fundo Naval atual: ${allocation['fundo_naval']:,.2f}

========================================
"""
        return report
    
    def get_monthly_report(self, year: int, month: int) -> str:
        """Generate a report for a specific month."""
        # Filter streams by month
        monthly_streams = [
            s for s in self.revenue_streams
            if s.date.startswith(f"{year:04d}-{month:02d}")
        ]
        
        monthly_total = sum(s.amount for s in monthly_streams)
        monthly_by_platform = {
            'amazon': sum(s.amount for s in monthly_streams if s.platform == 'amazon'),
            'apple': sum(s.amount for s in monthly_streams if s.platform == 'apple'),
            'youtube': sum(s.amount for s in monthly_streams if s.platform == 'youtube')
        }
        
        report = f"""
========================================
RELATÓRIO MENSAL - {month:02d}/{year:04d}
========================================

Receitas:
  Amazon:  ${monthly_by_platform['amazon']:,.2f}
  Apple:   ${monthly_by_platform['apple']:,.2f}
  YouTube: ${monthly_by_platform['youtube']:,.2f}
  ─────────────────────────────
  TOTAL:   ${monthly_total:,.2f}

Total de transações: {len(monthly_streams)}
========================================
"""
        return report


def main():
    """CLI interface for the financial tracker."""
    import sys
    
    tracker = FinancialFlowTracker()
    
    if len(sys.argv) < 2:
        print("Uso: financial_flow_tracker.py [start|status|add|snapshot]")
        sys.exit(1)
    
    command = sys.argv[1]
    
    if command == "start":
        print("LOG_V97.0 Financial Flow Tracker iniciado")
        print("Sistema pronto para rastreamento de receitas")
        
    elif command == "status":
        print(tracker.get_status_report())
        
    elif command == "add":
        # Example: add amazon 150.50 royalty
        if len(sys.argv) < 5:
            print("Uso: add [platform] [amount] [source_type]")
            sys.exit(1)
        
        platform = sys.argv[2]
        amount = float(sys.argv[3])
        source_type = sys.argv[4]
        
        tracker.add_revenue(platform, amount, source_type)
        print(f"Receita adicionada: {platform} ${amount:.2f} ({source_type})")
        
    elif command == "snapshot":
        snapshot = tracker.create_snapshot()
        print(f"Snapshot criado: ${snapshot.total_revenue:,.2f}")
        print(f"  Fundo Naval: ${snapshot.fundo_naval:,.2f}")
        
    elif command == "monthly":
        if len(sys.argv) < 4:
            print("Uso: monthly [year] [month]")
            sys.exit(1)
        year = int(sys.argv[2])
        month = int(sys.argv[3])
        print(tracker.get_monthly_report(year, month))
        
    else:
        print(f"Comando desconhecido: {command}")


if __name__ == "__main__":
    main()
