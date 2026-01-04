#!/usr/bin/env python3
"""
Revenue Allocator - LOG_V97.0 Component
Automatically allocates revenue to Capital de Giro, Fundo Naval, and Fundo Tera
"""

from typing import Dict, List
from dataclasses import dataclass
from datetime import datetime
import json


@dataclass
class AllocationRule:
    """Rule for allocating revenue."""
    name: str
    percentage: float  # 0.0-1.0
    description: str
    priority: int  # for ordering


@dataclass
class Allocation:
    """Single allocation record."""
    date: str
    total_amount: float
    capital_giro: float
    fundo_naval: float
    fundo_tera: float
    source: str  # "automatic", "manual", "adjustment"


class RevenueAllocator:
    """
    Manages revenue allocation according to LOG_V97.0 distribution model:
    - 30% Capital de Giro (Working Capital)
    - 50% Fundo Naval (Naval Fund for Barco Escola)
    - 20% Fundo Tera (Tera Fund for Hostels/Theaters)
    """
    
    # Tolerance for percentage validation (e.g., 0.299 + 0.500 + 0.201 = 1.00)
    PERCENTAGE_TOLERANCE = 0.01
    
    # Default allocation rules per LOG_V97.0
    DEFAULT_RULES = [
        AllocationRule(
            name="capital_giro",
            percentage=0.30,
            description="Capital de Giro - Reinvestment in advertising and campaigns",
            priority=1
        ),
        AllocationRule(
            name="fundo_naval",
            percentage=0.50,
            description="Fundo Naval - Accumulation for Barco Escola entry ($12k/month target)",
            priority=2
        ),
        AllocationRule(
            name="fundo_tera",
            percentage=0.20,
            description="Fundo Tera - Reserve for sustainable Hostels and Theaters",
            priority=3
        )
    ]
    
    # Milestones for the Naval Fund
    NAVAL_MILESTONES = [
        {"amount": 3000, "description": "Initial deposit secured"},
        {"amount": 7000, "description": "February target reached"},
        {"amount": 12000, "description": "Monthly target achieved - Barco Escola entry"},
        {"amount": 36000, "description": "Three months accumulated - Full security"},
        {"amount": 100000, "description": "One year operation fund - Sustainability"}
    ]
    
    def __init__(self, data_file: str = "allocation_data.json"):
        self.data_file = data_file
        self.rules = self.DEFAULT_RULES.copy()
        self.allocations: List[Allocation] = []
        self.totals = {
            "capital_giro": 0.0,
            "fundo_naval": 0.0,
            "fundo_tera": 0.0
        }
        self.load_data()
    
    def load_data(self) -> None:
        """Load allocation history from JSON."""
        try:
            with open(self.data_file, 'r') as f:
                data = json.load(f)
                
                # Load allocations
                for alloc_data in data.get('allocations', []):
                    allocation = Allocation(**alloc_data)
                    self.allocations.append(allocation)
                
                # Load totals
                self.totals = data.get('totals', self.totals)
        except FileNotFoundError:
            pass
    
    def save_data(self) -> None:
        """Save allocation history to JSON."""
        data = {
            'allocations': [
                {
                    'date': a.date,
                    'total_amount': a.total_amount,
                    'capital_giro': a.capital_giro,
                    'fundo_naval': a.fundo_naval,
                    'fundo_tera': a.fundo_tera,
                    'source': a.source
                }
                for a in self.allocations
            ],
            'totals': self.totals,
            'last_updated': datetime.now().isoformat()
        }
        with open(self.data_file, 'w') as f:
            json.dump(data, f, indent=2)
    
    def allocate_revenue(
        self,
        amount: float,
        source: str = "automatic"
    ) -> Allocation:
        """
        Allocate revenue according to default rules.
        
        Args:
            amount: Total revenue to allocate
            source: Source of allocation ("automatic", "manual", "adjustment")
            
        Returns:
            Allocation record
        """
        # Calculate allocations
        capital_giro = amount * 0.30
        fundo_naval = amount * 0.50
        fundo_tera = amount * 0.20
        
        # Create allocation record
        allocation = Allocation(
            date=datetime.now().isoformat(),
            total_amount=amount,
            capital_giro=capital_giro,
            fundo_naval=fundo_naval,
            fundo_tera=fundo_tera,
            source=source
        )
        
        # Update totals
        self.totals["capital_giro"] += capital_giro
        self.totals["fundo_naval"] += fundo_naval
        self.totals["fundo_tera"] += fundo_tera
        
        # Save allocation
        self.allocations.append(allocation)
        self.save_data()
        
        return allocation
    
    def allocate_custom(
        self,
        amount: float,
        capital_giro_pct: float,
        fundo_naval_pct: float,
        fundo_tera_pct: float
    ) -> Allocation:
        """
        Allocate revenue with custom percentages.
        
        Args:
            amount: Total revenue to allocate
            capital_giro_pct: Percentage for capital de giro (0.0-1.0)
            fundo_naval_pct: Percentage for fundo naval (0.0-1.0)
            fundo_tera_pct: Percentage for fundo tera (0.0-1.0)
            
        Returns:
            Allocation record
            
        Raises:
            ValueError: If percentages don't sum to 1.0
        """
        total_pct = capital_giro_pct + fundo_naval_pct + fundo_tera_pct
        if abs(total_pct - 1.0) > self.PERCENTAGE_TOLERANCE:
            raise ValueError(f"Percentages must sum to 1.0, got {total_pct}")
        
        allocation = Allocation(
            date=datetime.now().isoformat(),
            total_amount=amount,
            capital_giro=amount * capital_giro_pct,
            fundo_naval=amount * fundo_naval_pct,
            fundo_tera=amount * fundo_tera_pct,
            source="manual"
        )
        
        # Update totals
        self.totals["capital_giro"] += allocation.capital_giro
        self.totals["fundo_naval"] += allocation.fundo_naval
        self.totals["fundo_tera"] += allocation.fundo_tera
        
        # Save allocation
        self.allocations.append(allocation)
        self.save_data()
        
        return allocation
    
    def get_next_naval_milestone(self) -> Dict:
        """Get the next milestone for the Naval Fund."""
        current_amount = self.totals["fundo_naval"]
        
        for milestone in self.NAVAL_MILESTONES:
            if current_amount < milestone["amount"]:
                remaining = milestone["amount"] - current_amount
                progress = (current_amount / milestone["amount"]) * 100
                
                return {
                    "target": milestone["amount"],
                    "description": milestone["description"],
                    "remaining": remaining,
                    "progress": progress,
                    "current": current_amount
                }
        
        # All milestones reached
        return {
            "target": self.NAVAL_MILESTONES[-1]["amount"],
            "description": "All milestones achieved! 🎉",
            "remaining": 0,
            "progress": 100.0,
            "current": current_amount
        }
    
    def get_allocation_summary(self) -> str:
        """Generate a summary of current allocations."""
        total_allocated = sum(self.totals.values())
        
        report = f"""
========================================
LOG_V97.0 - REVENUE ALLOCATION SUMMARY
========================================
Data: {datetime.now().strftime('%d/%m/%Y %H:%M')}

TOTAIS ACUMULADOS:
  Capital de Giro: ${self.totals['capital_giro']:,.2f} (30%)
  Fundo Naval:     ${self.totals['fundo_naval']:,.2f} (50%)
  Fundo Tera:      ${self.totals['fundo_tera']:,.2f} (20%)
  ─────────────────────────────────────────
  TOTAL ALOCADO:   ${total_allocated:,.2f}

"""
        
        # Naval Fund milestone progress
        milestone = self.get_next_naval_milestone()
        report += f"""
PROGRESSO FUNDO NAVAL (BARCO ESCOLA):
  Meta atual: ${milestone['target']:,.2f} - {milestone['description']}
  Progresso: {milestone['progress']:.1f}%
  Faltam: ${milestone['remaining']:,.2f}

"""
        
        # Recent allocations
        report += "ÚLTIMAS 5 ALOCAÇÕES:\n"
        recent = self.allocations[-5:] if len(self.allocations) >= 5 else self.allocations
        for alloc in reversed(recent):
            date_str = datetime.fromisoformat(alloc.date).strftime('%d/%m/%Y')
            report += f"\n  {date_str} - ${alloc.total_amount:,.2f}"
            report += f"\n    CG: ${alloc.capital_giro:,.2f} | "
            report += f"FN: ${alloc.fundo_naval:,.2f} | "
            report += f"FT: ${alloc.fundo_tera:,.2f}\n"
        
        report += """
========================================
"""
        return report
    
    def get_monthly_breakdown(self, year: int, month: int) -> str:
        """Generate allocation breakdown for a specific month."""
        monthly_allocations = [
            a for a in self.allocations
            if a.date.startswith(f"{year:04d}-{month:02d}")
        ]
        
        if not monthly_allocations:
            return f"Nenhuma alocação encontrada para {month:02d}/{year:04d}"
        
        total = sum(a.total_amount for a in monthly_allocations)
        capital_giro = sum(a.capital_giro for a in monthly_allocations)
        fundo_naval = sum(a.fundo_naval for a in monthly_allocations)
        fundo_tera = sum(a.fundo_tera for a in monthly_allocations)
        
        report = f"""
========================================
ALOCAÇÕES - {month:02d}/{year:04d}
========================================

Total alocado no mês: ${total:,.2f}

Distribuição:
  Capital de Giro: ${capital_giro:,.2f}
  Fundo Naval:     ${fundo_naval:,.2f}
  Fundo Tera:      ${fundo_tera:,.2f}

Número de alocações: {len(monthly_allocations)}

Meta Fevereiro (se aplicável): $7,000.00
{'✅ Meta atingida!' if month == 2 and total >= 7000 else ''}

Meta Março+ (Barco Escola): $12,000.00/mês
{'✅ Meta atingida!' if month >= 3 and total >= 12000 else ''}
========================================
"""
        return report
    
    def project_naval_fund(self, monthly_revenue: float, months: int) -> Dict:
        """Project Naval Fund growth over time."""
        current = self.totals["fundo_naval"]
        monthly_allocation = monthly_revenue * 0.50  # 50% to Naval Fund
        
        projected_total = current + (monthly_allocation * months)
        
        return {
            "current": current,
            "monthly_revenue": monthly_revenue,
            "monthly_allocation": monthly_allocation,
            "months": months,
            "projected_total": projected_total,
            "barco_escola_ready": projected_total >= 12000
        }


def main():
    """CLI interface for revenue allocator."""
    import sys
    
    allocator = RevenueAllocator()
    
    if len(sys.argv) < 2:
        print("Uso: revenue_allocator.py [summary|allocate|milestone|project|monthly]")
        sys.exit(1)
    
    command = sys.argv[1]
    
    if command == "summary":
        print(allocator.get_allocation_summary())
        
    elif command == "allocate":
        if len(sys.argv) < 3:
            print("Uso: allocate [amount]")
            sys.exit(1)
        
        amount = float(sys.argv[2])
        allocation = allocator.allocate_revenue(amount)
        
        print(f"\n✅ Receita alocada: ${amount:,.2f}")
        print(f"  Capital de Giro: ${allocation.capital_giro:,.2f}")
        print(f"  Fundo Naval: ${allocation.fundo_naval:,.2f}")
        print(f"  Fundo Tera: ${allocation.fundo_tera:,.2f}\n")
        
    elif command == "milestone":
        milestone = allocator.get_next_naval_milestone()
        print(f"\n🎯 Próxima meta: ${milestone['target']:,.2f}")
        print(f"   {milestone['description']}")
        print(f"   Progresso: {milestone['progress']:.1f}%")
        print(f"   Faltam: ${milestone['remaining']:,.2f}\n")
        
    elif command == "project":
        if len(sys.argv) < 4:
            print("Uso: project [monthly_revenue] [months]")
            sys.exit(1)
        
        monthly_revenue = float(sys.argv[2])
        months = int(sys.argv[3])
        
        projection = allocator.project_naval_fund(monthly_revenue, months)
        
        print(f"\n📊 Projeção Fundo Naval ({months} meses)")
        print(f"   Atual: ${projection['current']:,.2f}")
        print(f"   Alocação mensal: ${projection['monthly_allocation']:,.2f}")
        print(f"   Projetado: ${projection['projected_total']:,.2f}")
        print(f"   Barco Escola: {'✅ Pronto!' if projection['barco_escola_ready'] else '❌ Ainda não'}\n")
        
    elif command == "monthly":
        if len(sys.argv) < 4:
            print("Uso: monthly [year] [month]")
            sys.exit(1)
        
        year = int(sys.argv[2])
        month = int(sys.argv[3])
        print(allocator.get_monthly_breakdown(year, month))
        
    else:
        print(f"Comando desconhecido: {command}")


if __name__ == "__main__":
    main()
