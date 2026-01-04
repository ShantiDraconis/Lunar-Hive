#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "$0")/.." && pwd)"
INFRA_DIR="${ROOT_DIR}/01_DIGITAL_INFRASTRUCTURE"
BIOTECH_DIR="${ROOT_DIR}/02_BIOTECH_LEGACY"
VOID_MARK="VOID"
APPROVAL_FLAG="${KILL_SWITCH_APPROVED:-}"

if [[ "$APPROVAL_FLAG" != "yes" ]]; then
  echo "Falta autorização: defina KILL_SWITCH_APPROVED=yes" >&2
  exit 1
fi

if [[ "${1:-}" != "--breach" ]]; then
  echo "Uso: $0 --breach \"motivo\" (motivo: letras, números, _ ou -)" >&2
  exit 1
fi

reason="${2:-ethical_violation}"
if [[ -z "$reason" ]]; then
  echo "Motivo inválido. Não pode ser vazio." >&2
  exit 1
fi
if [[ ! "$reason" =~ ^[a-zA-Z0-9_-]+$ ]]; then
  echo "Motivo inválido. Use somente [a-zA-Z0-9_-]." >&2
  exit 1
fi

mark_void() {
  local target_dir="$1"
  if [[ ! -d "$target_dir" ]]; then
    echo "Diretório não encontrado: $target_dir" >&2
    exit 1
  fi
  local resolved
  resolved="$(realpath "$target_dir")"
  if [[ "$resolved" != "${ROOT_DIR}/"* ]]; then
    echo "Caminho fora do repositório bloqueado: $resolved" >&2
    exit 1
  fi
  echo "$reason" > "${resolved}/${VOID_MARK}"
}

# Lógica: se o sucessor quebrar a ética, ambas as pastas são marcadas como VOID.
mark_void "$INFRA_DIR"
mark_void "$BIOTECH_DIR"

echo "Acesso marcado como ${VOID_MARK} em:"
echo " - ${INFRA_DIR}"
echo " - ${BIOTECH_DIR}"
