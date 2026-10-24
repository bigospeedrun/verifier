set -euo pipefail

if [ "${GITHUB_ACTIONS:-}" != "true" ]; then
  echo 'Run the Lean check on GitHub Actions, as required by AGENTS.md.' >&2
  exit 2
fi

package_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
repo_dir=$(git -C "$package_dir" rev-parse --show-toplevel)
check_dir=$(mktemp -d)
trap 'rm -rf "$check_dir"' EXIT

cp "$repo_dir/challenges/catalan/Statement.lean" "$check_dir/Statement.lean"
cp "$package_dir/code/Validation.lean" "$check_dir/Validation.lean"
printf '%s\n' 'leanprover/lean4:v4.35.0-rc2' > "$check_dir/lean-toolchain"
cat > "$check_dir/lakefile.toml" <<'TOML'
name = "catalanStatementCheck"
version = "0.1.0"
defaultTargets = ["Statement", "Validation"]

[[require]]
name = "mathlib"
git = "https://github.com/leanprover-community/mathlib4.git"
rev = "065356127b1dc0016f66b7283ce0ce2c4055aa55"

[[lean_lib]]
name = "Statement"

[[lean_lib]]
name = "Validation"
TOML

cd "$check_dir"
lake update
lake exe cache get Mathlib.Analysis.SpecialFunctions.Pow.Real \
  Mathlib.Topology.Algebra.InfiniteSum.Real \
  Mathlib.Order.Filter.AtTopBot.Basic Mathlib.Tactic
lake build Statement
lake env lean -DwarningAsError=true Validation.lean
