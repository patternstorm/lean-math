import Universe
import Logic
import Universals.Dyads.Operations.Unary.Subsume.Operation

/-!
# Subsumptivity — the sub-universal properties of `subsume`

Three theorems:

- `subsumptivity` — given `e₁: U₁' <: U₁` and `e₂: U₂' <: U₂`, the dyad universal `U₁' ⧓ U₂'` is a sub-universal of `U₁ ⧓ U₂`, via `subsume`.
- `subsumptivity_left` — left-only refinement (right component via `refl_subuniversal`).
- `subsumptivity_right` — right-only refinement (left component via `refl_subuniversal`).
-/

namespace Universe
namespace Dyads

open Logic
open Logic.PC₁
open Logic.ND

-- # Helper: action of subsume on the dyad constructor
-- From subsume_def + reflexivity of the extension at the matching witnesses:
--   subsume e₁ e₂ (a ⋈ b) =ₗₓₗ (e₁ a ⋈ e₂ b).
-- The extension graph holds because (a ⋈ b) =ₗₓₗ (a ⋈ b) (refl) and
-- (e₁ a ⋈ e₂ b) =ₗₓₗ (e₁ a ⋈ e₂ b) (refl), so a = a, b = b witness the ∃.
--
-- ------------------------
-- TODO: move to a property of the subsume operation
-- ------------------------
-- Proof by Claude Opus 4.7, 2026-04-19
theorem subsume_bind {U₁' U₁ U₂' U₂: Universal} (e₁: U₁' <: U₁) (e₂: U₂' <: U₂): ∀ (a: U₁'.Particular), ∀ (b: U₂'.Particular), subsume_sym e₁ e₂ (a ⋈ b) =ₗₓₗ (e₁.embedding a ⋈ e₂.embedding b) := by forall_intro
  variable(a: U₁'.Particular)
  variable(b: U₂'.Particular)
  -- Witness the extension graph at (a ⋈ b) for the image (e₁ a ⋈ e₂ b)
  have h₁: (a ⋈ b) =ₗₓₗ (a ⋈ b) := by forall_elim eq_refl, (a ⋈ b)
  have h₂: (e₁.embedding a ⋈ e₂.embedding b) =ₗₓₗ (e₁.embedding a ⋈ e₂.embedding b) := by forall_elim eq_refl, (e₁.embedding a ⋈ e₂.embedding b)
  have h₃: (a ⋈ b) =ₗₓₗ (a ⋈ b) ∧ (e₁.embedding a ⋈ e₂.embedding b) =ₗₓₗ (e₁.embedding a ⋈ e₂.embedding b) := by and_intro h₁, h₂
  have h₄: ∃ (b': U₂'.Particular), (a ⋈ b) =ₗₓₗ (a ⋈ b') ∧ (e₁.embedding a ⋈ e₂.embedding b) =ₗₓₗ (e₁.embedding a ⋈ e₂.embedding b') := by exists_intro h₃, b
  have h₅: ∃ (a': U₁'.Particular), ∃ (b': U₂'.Particular), (a ⋈ b) =ₗₓₗ (a' ⋈ b') ∧ (e₁.embedding a ⋈ e₂.embedding b) =ₗₓₗ (e₁.embedding a' ⋈ e₂.embedding b') := by exists_intro h₄, a
  -- h₅ is ((subsume_ext e₁ e₂).pred (a ⋈ b)).pred (e₁ a ⋈ e₂ b) unfolded
  -- Use subsume_def to conclude
  have h₆: ∀ (x: (U₁' ⧓ U₂').Particular), ∀ (y: (U₁ ⧓ U₂).Particular), (subsume_sym e₁ e₂ x =ₗₓₗ y) ↔ ((subsume_ext e₁ e₂).pred x).pred y := subsume_def e₁ e₂
  have h₇: ∀ (y: (U₁ ⧓ U₂).Particular), (subsume_sym e₁ e₂ (a ⋈ b) =ₗₓₗ y) ↔ ((subsume_ext e₁ e₂).pred (a ⋈ b)).pred y := by forall_elim h₆, (a ⋈ b)
  have h₈: (subsume_sym e₁ e₂ (a ⋈ b) =ₗₓₗ (e₁.embedding a ⋈ e₂.embedding b)) ↔ ((subsume_ext e₁ e₂).pred (a ⋈ b)).pred (e₁.embedding a ⋈ e₂.embedding b) := by forall_elim h₇, (e₁.embedding a ⋈ e₂.embedding b)
  have h₉: subsume_sym e₁ e₂ (a ⋈ b) =ₗₓₗ (e₁.embedding a ⋈ e₂.embedding b) := PC₀.deductive_eq_r2l h₈ h₅
  iterate h₉

-- ------------------------
-- TODO: fix (X ⧓ Y).Particular to (X ⋈ Y)
-- ------------------------

-- # Subsumptivity — U₁' ⧓ U₂' <: U₁ ⧓ U₂ via subsume
-- preserves_eq: d₁' =ₗₓₗ d₂' ↔ subsume d₁' =ₗₓₗ subsume d₂'.
-- Forward: `(subsume e₁ e₂).cong` (derived UnaryOperation congruence).
-- Backward: chain `subsume d_i =ₗₓₗ (e₁ a_i ⋈ e₂ b_i)` via exhaustiveness +
-- Leibniz + subsume_bind, then apply eq_def forward + e_i.preserves_eq backward +
-- eq_def backward + Leibniz to recover d₁' =ₗₓₗ d₂'.
--
-- Proof by Claude Opus 4.7, 2026-04-19
noncomputable def subsumptivity {U₁' U₁ U₂' U₂: Universal} (e₁: U₁' <: U₁) (e₂: U₂' <: U₂): (U₁' ⧓ U₂') <: (U₁ ⧓ U₂) :=
  let subsume: (U₁' ⧓ U₂') ⟴ (U₁ ⧓ U₂) := subsume e₁ e₂
  let preserves_eq: ∀ (d₁': (U₁' ⧓ U₂').Particular), ∀ (d₂': (U₁' ⧓ U₂').Particular), d₁' =ₗₓₗ d₂' ↔ (subsume d₁' =ₗₓₗ subsume d₂') := by forall_intro
    variable(d₁': (U₁' ⧓ U₂').Particular)
    variable(d₂': (U₁' ⧓ U₂').Particular)
    -- Forward: congruence of the UnaryOperation.
    -- ------------------------
    -- TODO: fix clauses naming
    -- ------------------------
    have fwd: d₁' =ₗₓₗ d₂' → subsume d₁' =ₗₓₗ subsume d₂' := by
      have h₁: ∀ (x₂: (U₁' ⧓ U₂').Particular), d₁' =ₗₓₗ x₂ → (subsume d₁' =ₗₓₗ subsume x₂) := by forall_elim subsume.cong, d₁'
      have h₂: d₁' =ₗₓₗ d₂' → (subsume d₁' =ₗₓₗ subsume d₂') := by forall_elim h₁, d₂'
      iterate h₂
    -- Backward: injectivity via exhaustiveness + subsume_bind + component preserves_eq.
    have bwd: subsume d₁' =ₗₓₗ subsume d₂' → d₁' =ₗₓₗ d₂' := by
      assume(h₁: subsume d₁' =ₗₓₗ subsume d₂')
      -- Decompose d₁' and d₂' via exhaustiveness
      have h₂: ∃ (a: U₁'.Particular), ∃ (b: U₂'.Particular), d₁' 🟰 (a ⋈ b) := by forall_elim exhaustiveness, d₁'
      have ⟨(a₁: U₁'.Particular), (h₃: ∃ (b: U₂'.Particular), d₁' 🟰 (a₁ ⋈ b))⟩ := exists_elim h₂
      have ⟨(b₁: U₂'.Particular), (h₄: d₁' 🟰 (a₁ ⋈ b₁))⟩ := exists_elim h₃
      have h₅: ∃ (a: U₁'.Particular), ∃ (b: U₂'.Particular), d₂' 🟰 (a ⋈ b) := by forall_elim exhaustiveness, d₂'
      have ⟨(a₂: U₁'.Particular), (h₆: ∃ (b: U₂'.Particular), d₂' 🟰 (a₂ ⋈ b))⟩ := exists_elim h₅
      have ⟨(b₂: U₂'.Particular), (h₇: d₂' 🟰 (a₂ ⋈ b₂))⟩ := exists_elim h₆
      -- subsume_bind at (a₁, b₁) and (a₂, b₂)
      have h₈: ∀ (b: U₂'.Particular), subsume (a₁ ⋈ b) =ₗₓₗ (e₁.embedding a₁ ⋈ e₂.embedding b) := by forall_elim subsume_bind e₁ e₂, a₁
      have h₉: subsume (a₁ ⋈ b₁) =ₗₓₗ (e₁.embedding a₁ ⋈ e₂.embedding b₁) := by forall_elim h₈, b₁
      have h₁₀: ∀ (b: U₂'.Particular), subsume (a₂ ⋈ b) =ₗₓₗ (e₁.embedding a₂ ⋈ e₂.embedding b) := by forall_elim subsume_bind e₁ e₂, a₂
      have h₁₁: subsume (a₂ ⋈ b₂) =ₗₓₗ (e₁.embedding a₂ ⋈ e₂.embedding b₂) := by forall_elim h₁₀, b₂
      -- Transfer d_i 🟰 (a_i ⋈ b_i) into subsume d_i =ₗₓₗ subsume (a_i ⋈ b_i) via Leibniz
      let pred₁: (U₁' ⧓ U₂').Particular → Prop := (x: (U₁' ⧓ U₂').Particular ↦ subsume d₁' =ₗₓₗ subsume x)
      have h₁₂: ∀ (x: (U₁' ⧓ U₂').Particular), ∀ (y: (U₁' ⧓ U₂').Particular), x 🟰 y → (pred₁ x ↔ pred₁ y) := by forall_elim leibniz_eq_subs, pred₁
      have h₁₃: ∀ (y: (U₁' ⧓ U₂').Particular), d₁' 🟰 y → (pred₁ d₁' ↔ pred₁ y) := by forall_elim h₁₂, d₁'
      have h₁₄: d₁' 🟰 (a₁ ⋈ b₁) → (pred₁ d₁' ↔ pred₁ (a₁ ⋈ b₁)) := by forall_elim h₁₃, (a₁ ⋈ b₁)
      have h₁₅: pred₁ d₁' ↔ pred₁ (a₁ ⋈ b₁) := by modus_ponens h₁₄, h₄
      -- pred₁ d₁' = (s d₁' =ₗₓₗ s d₁') which holds by refl on s d₁'
      have h₁₆: subsume d₁' =ₗₓₗ subsume d₁' := by forall_elim eq_refl, (subsume d₁')
      have h₁₇: subsume d₁' =ₗₓₗ subsume (a₁ ⋈ b₁) := PC₀.deductive_eq_l2r h₁₅ h₁₆
      let pred₂: (U₁' ⧓ U₂').Particular → Prop := (x: (U₁' ⧓ U₂').Particular ↦ subsume d₂' =ₗₓₗ subsume x)
      have h₁₈: ∀ (x: (U₁' ⧓ U₂').Particular), ∀ (y: (U₁' ⧓ U₂').Particular), x 🟰 y → (pred₂ x ↔ pred₂ y) := by forall_elim leibniz_eq_subs, pred₂
      have h₁₉: ∀ (y: (U₁' ⧓ U₂').Particular), d₂' 🟰 y → (pred₂ d₂' ↔ pred₂ y) := by forall_elim h₁₈, d₂'
      have h₂₀: d₂' 🟰 (a₂ ⋈ b₂) → (pred₂ d₂' ↔ pred₂ (a₂ ⋈ b₂)) := by forall_elim h₁₉, (a₂ ⋈ b₂)
      have h₂₁: pred₂ d₂' ↔ pred₂ (a₂ ⋈ b₂) := by modus_ponens h₂₀, h₇
      have h₂₂: subsume d₂' =ₗₓₗ subsume d₂' := by forall_elim eq_refl, (subsume d₂')
      have h₂₃: subsume d₂' =ₗₓₗ subsume (a₂ ⋈ b₂) := PC₀.deductive_eq_l2r h₂₁ h₂₂
      -- Chain: (e₁ a₁ ⋈ e₂ b₁) =ₗₓₗ s (a₁⋈b₁) =ₗₓₗ s d₁' =ₗₓₗ s d₂' =ₗₓₗ s (a₂⋈b₂) =ₗₓₗ (e₁ a₂ ⋈ e₂ b₂)
      have h₂₄: subsume (a₁ ⋈ b₁) =ₗₓₗ (e₁.embedding a₁ ⋈ e₂.embedding b₁) → (e₁.embedding a₁ ⋈ e₂.embedding b₁) =ₗₓₗ subsume (a₁ ⋈ b₁) := by forall_elim eq_sym, (subsume (a₁ ⋈ b₁)), (e₁.embedding a₁ ⋈ e₂.embedding b₁)
      have h₂₅: (e₁.embedding a₁ ⋈ e₂.embedding b₁) =ₗₓₗ subsume (a₁ ⋈ b₁) := by modus_ponens h₂₄, h₉
      have h₂₆: subsume d₁' =ₗₓₗ subsume (a₁ ⋈ b₁) → subsume (a₁ ⋈ b₁) =ₗₓₗ subsume d₁' := by forall_elim eq_sym, (subsume d₁'), (subsume (a₁ ⋈ b₁))
      have h₂₇: subsume (a₁ ⋈ b₁) =ₗₓₗ subsume d₁' := by modus_ponens h₂₆, h₁₇
      have h₂₈: (e₁.embedding a₁ ⋈ e₂.embedding b₁) =ₗₓₗ subsume (a₁ ⋈ b₁) ∧ subsume (a₁ ⋈ b₁) =ₗₓₗ subsume d₁' := by and_intro h₂₅, h₂₇
      have h₂₉: (e₁.embedding a₁ ⋈ e₂.embedding b₁) =ₗₓₗ subsume (a₁ ⋈ b₁) ∧ subsume (a₁ ⋈ b₁) =ₗₓₗ subsume d₁' → (e₁.embedding a₁ ⋈ e₂.embedding b₁) =ₗₓₗ subsume d₁' := by forall_elim eq_trans, (e₁.embedding a₁ ⋈ e₂.embedding b₁), (subsume (a₁ ⋈ b₁)), (subsume d₁')
      have h₃₀: (e₁.embedding a₁ ⋈ e₂.embedding b₁) =ₗₓₗ subsume d₁' := by modus_ponens h₂₉, h₂₈
      have h₃₁: (e₁.embedding a₁ ⋈ e₂.embedding b₁) =ₗₓₗ subsume d₁' ∧ subsume d₁' =ₗₓₗ subsume d₂' := by and_intro h₃₀, h₁
      have h₃₂: (e₁.embedding a₁ ⋈ e₂.embedding b₁) =ₗₓₗ subsume d₁' ∧ subsume d₁' =ₗₓₗ subsume d₂' → (e₁.embedding a₁ ⋈ e₂.embedding b₁) =ₗₓₗ subsume d₂' := by forall_elim eq_trans, (e₁.embedding a₁ ⋈ e₂.embedding b₁), (subsume d₁'), (subsume d₂')
      have h₃₃: (e₁.embedding a₁ ⋈ e₂.embedding b₁) =ₗₓₗ subsume d₂' := by modus_ponens h₃₂, h₃₁
      have h₃₄: (e₁.embedding a₁ ⋈ e₂.embedding b₁) =ₗₓₗ subsume d₂' ∧ subsume d₂' =ₗₓₗ subsume (a₂ ⋈ b₂) := by and_intro h₃₃, h₂₃
      have h₃₅: (e₁.embedding a₁ ⋈ e₂.embedding b₁) =ₗₓₗ subsume d₂' ∧ subsume d₂' =ₗₓₗ subsume (a₂ ⋈ b₂) → (e₁.embedding a₁ ⋈ e₂.embedding b₁) =ₗₓₗ subsume (a₂ ⋈ b₂) := by forall_elim eq_trans, (e₁.embedding a₁ ⋈ e₂.embedding b₁), (subsume d₂'), (subsume (a₂ ⋈ b₂))
      have h₃₆: (e₁.embedding a₁ ⋈ e₂.embedding b₁) =ₗₓₗ subsume (a₂ ⋈ b₂) := by modus_ponens h₃₅, h₃₄
      have h₃₇: (e₁.embedding a₁ ⋈ e₂.embedding b₁) =ₗₓₗ subsume (a₂ ⋈ b₂) ∧ subsume (a₂ ⋈ b₂) =ₗₓₗ (e₁.embedding a₂ ⋈ e₂.embedding b₂) := by and_intro h₃₆, h₁₁
      have h₃₈: (e₁.embedding a₁ ⋈ e₂.embedding b₁) =ₗₓₗ subsume (a₂ ⋈ b₂) ∧ subsume (a₂ ⋈ b₂) =ₗₓₗ (e₁.embedding a₂ ⋈ e₂.embedding b₂) → (e₁.embedding a₁ ⋈ e₂.embedding b₁) =ₗₓₗ (e₁.embedding a₂ ⋈ e₂.embedding b₂) := by forall_elim eq_trans, (e₁.embedding a₁ ⋈ e₂.embedding b₁), (subsume (a₂ ⋈ b₂)), (e₁.embedding a₂ ⋈ e₂.embedding b₂)
      have h₃₉: (e₁.embedding a₁ ⋈ e₂.embedding b₁) =ₗₓₗ (e₁.embedding a₂ ⋈ e₂.embedding b₂) := by modus_ponens h₃₈, h₃₇
      -- Apply eq_def (forward) to extract component equalities
      have h₄₀: ∀ (b'': U₂.Particular), ∀ (a''': U₁.Particular), ∀ (b''': U₂.Particular), (e₁.embedding a₁ ⋈ b'') =ₗₓₗ (a''' ⋈ b''') ↔ e₁.embedding a₁ =₍U₁₎ a''' ∧ b'' =₍U₂₎ b''' := by forall_elim eq_def, (e₁.embedding a₁)
      have h₄₁: ∀ (a''': U₁.Particular), ∀ (b''': U₂.Particular), (e₁.embedding a₁ ⋈ e₂.embedding b₁) =ₗₓₗ (a''' ⋈ b''') ↔ e₁.embedding a₁ =₍U₁₎ a''' ∧ e₂.embedding b₁ =₍U₂₎ b''' := by forall_elim h₄₀, (e₂.embedding b₁)
      have h₄₂: ∀ (b''': U₂.Particular), (e₁.embedding a₁ ⋈ e₂.embedding b₁) =ₗₓₗ (e₁.embedding a₂ ⋈ b''') ↔ e₁.embedding a₁ =₍U₁₎ e₁.embedding a₂ ∧ e₂.embedding b₁ =₍U₂₎ b''' := by forall_elim h₄₁, (e₁.embedding a₂)
      have h₄₃: (e₁.embedding a₁ ⋈ e₂.embedding b₁) =ₗₓₗ (e₁.embedding a₂ ⋈ e₂.embedding b₂) ↔ e₁.embedding a₁ =₍U₁₎ e₁.embedding a₂ ∧ e₂.embedding b₁ =₍U₂₎ e₂.embedding b₂ := by forall_elim h₄₂, (e₂.embedding b₂)
      have h₄₄: e₁.embedding a₁ =₍U₁₎ e₁.embedding a₂ ∧ e₂.embedding b₁ =₍U₂₎ e₂.embedding b₂ := PC₀.deductive_eq_l2r h₄₃ h₃₉
      have h₄₅: e₁.embedding a₁ =₍U₁₎ e₁.embedding a₂ := by and_elim h₄₄
      have h₄₆: e₂.embedding b₁ =₍U₂₎ e₂.embedding b₂ := by and_elim h₄₄
      -- Apply e_i.preserves_eq (backward) to recover component equalities
      have h₄₇: ∀ (y: U₁'.Particular), a₁ =₍U₁'₎ y ↔ (e₁.embedding a₁ =₍U₁₎ e₁.embedding y) := by forall_elim e₁.preserves_eq, a₁
      have h₄₈: a₁ =₍U₁'₎ a₂ ↔ (e₁.embedding a₁ =₍U₁₎ e₁.embedding a₂) := by forall_elim h₄₇, a₂
      have h₄₉: a₁ =₍U₁'₎ a₂ := PC₀.deductive_eq_r2l h₄₈ h₄₅
      have h₅₀: ∀ (y: U₂'.Particular), b₁ =₍U₂'₎ y ↔ (e₂.embedding b₁ =₍U₂₎ e₂.embedding y) := by forall_elim e₂.preserves_eq, b₁
      have h₅₁: b₁ =₍U₂'₎ b₂ ↔ (e₂.embedding b₁ =₍U₂₎ e₂.embedding b₂) := by forall_elim h₅₀, b₂
      have h₅₂: b₁ =₍U₂'₎ b₂ := PC₀.deductive_eq_r2l h₅₁ h₄₆
      -- Apply eq_def (backward) to get (a₁ ⋈ b₁) =ₗₓₗ (a₂ ⋈ b₂)
      have h₅₃: ∀ (b₁'': U₂'.Particular), ∀ (a₂'': U₁'.Particular), ∀ (b₂'': U₂'.Particular), (a₁ ⋈ b₁'') =ₗₓₗ (a₂'' ⋈ b₂'') ↔ a₁ =₍U₁'₎ a₂'' ∧ b₁'' =₍U₂'₎ b₂'' := by forall_elim eq_def, a₁
      have h₅₄: ∀ (a₂'': U₁'.Particular), ∀ (b₂'': U₂'.Particular), (a₁ ⋈ b₁) =ₗₓₗ (a₂'' ⋈ b₂'') ↔ a₁ =₍U₁'₎ a₂'' ∧ b₁ =₍U₂'₎ b₂'' := by forall_elim h₅₃, b₁
      have h₅₅: ∀ (b₂'': U₂'.Particular), (a₁ ⋈ b₁) =ₗₓₗ (a₂ ⋈ b₂'') ↔ a₁ =₍U₁'₎ a₂ ∧ b₁ =₍U₂'₎ b₂'' := by forall_elim h₅₄, a₂
      have h₅₆: (a₁ ⋈ b₁) =ₗₓₗ (a₂ ⋈ b₂) ↔ a₁ =₍U₁'₎ a₂ ∧ b₁ =₍U₂'₎ b₂ := by forall_elim h₅₅, b₂
      have h₅₇: a₁ =₍U₁'₎ a₂ ∧ b₁ =₍U₂'₎ b₂ := by and_intro h₄₉, h₅₂
      have h₅₈: (a₁ ⋈ b₁) =ₗₓₗ (a₂ ⋈ b₂) := PC₀.deductive_eq_r2l h₅₆ h₅₇
      -- Transfer back to d₁' =ₗₓₗ d₂' via Leibniz
      let pred₃: (U₁' ⧓ U₂').Particular → Prop := (x: (U₁' ⧓ U₂').Particular ↦ x =ₗₓₗ (a₂ ⋈ b₂))
      have h₅₉: ∀ (x: (U₁' ⧓ U₂').Particular), ∀ (y: (U₁' ⧓ U₂').Particular), x 🟰 y → (pred₃ x ↔ pred₃ y) := by forall_elim leibniz_eq_subs, pred₃
      have h₆₀: ∀ (y: (U₁' ⧓ U₂').Particular), d₁' 🟰 y → (pred₃ d₁' ↔ pred₃ y) := by forall_elim h₅₉, d₁'
      have h₆₁: d₁' 🟰 (a₁ ⋈ b₁) → (pred₃ d₁' ↔ pred₃ (a₁ ⋈ b₁)) := by forall_elim h₆₀, (a₁ ⋈ b₁)
      have h₆₂: pred₃ d₁' ↔ pred₃ (a₁ ⋈ b₁) := by modus_ponens h₆₁, h₄
      have h₆₃: d₁' =ₗₓₗ (a₂ ⋈ b₂) := PC₀.deductive_eq_r2l h₆₂ h₅₈
      let pred₄: (U₁' ⧓ U₂').Particular → Prop := (x: (U₁' ⧓ U₂').Particular ↦ d₁' =ₗₓₗ x)
      have h₆₄: ∀ (x: (U₁' ⧓ U₂').Particular), ∀ (y: (U₁' ⧓ U₂').Particular), x 🟰 y → (pred₄ x ↔ pred₄ y) := by forall_elim leibniz_eq_subs, pred₄
      have h₆₅: ∀ (y: (U₁' ⧓ U₂').Particular), d₂' 🟰 y → (pred₄ d₂' ↔ pred₄ y) := by forall_elim h₆₄, d₂'
      have h₆₆: d₂' 🟰 (a₂ ⋈ b₂) → (pred₄ d₂' ↔ pred₄ (a₂ ⋈ b₂)) := by forall_elim h₆₅, (a₂ ⋈ b₂)
      have h₆₇: pred₄ d₂' ↔ pred₄ (a₂ ⋈ b₂) := by modus_ponens h₆₆, h₇
      have h₆₈: d₁' =ₗₓₗ d₂' := PC₀.deductive_eq_r2l h₆₇ h₆₃
      iterate h₆₈
    have result: d₁' =ₗₓₗ d₂' ↔ (subsume d₁' =ₗₓₗ subsume d₂') := by iff_intro fwd, bwd
    iterate result
  { embedding := subsume, preserves_eq := preserves_eq }

-- # Subsumptivity (left) — only the left component is refined
-- Uses `refl_subuniversal` on the right.
noncomputable def subsumptivity_left {U₁' U₁ U₂: Universal} (e: U₁' <: U₁): (U₁' ⧓ U₂) <: (U₁ ⧓ U₂) :=
  subsumptivity e (subuniversal_refl U₂)

-- # Subsumptivity (right) — only the right component is refined
-- Uses `refl_subuniversal` on the left.
noncomputable def subsumptivity_right {U₁ U₂' U₂: Universal} (e: U₂' <: U₂): (U₁ ⧓ U₂') <: (U₁ ⧓ U₂) :=
  subsumptivity (subuniversal_refl U₁) e

end Dyads
end Universe
