import AlgorithmicFreeEnergy.ConcreteCore

namespace AlgorithmicFreeEnergy

universe u v

noncomputable section

/-- Concrete binary codewords for prefix-machine syntax. -/
abbrev BitCode := List Bool

/-- One code is a prefix of another when the second extends the first by some suffix. -/
def codeIsPrefix (c₁ c₂ : BitCode) : Prop :=
  ∃ suffix : BitCode, c₂ = c₁ ++ suffix

theorem codeIsPrefix_refl (c : BitCode) : codeIsPrefix c c := by
  refine ⟨[], ?_⟩
  simp

theorem codeIsPrefix_trans {c₁ c₂ c₃ : BitCode} :
    codeIsPrefix c₁ c₂ → codeIsPrefix c₂ c₃ → codeIsPrefix c₁ c₃ := by
  intro h₁₂ h₂₃
  rcases h₁₂ with ⟨s₁₂, rfl⟩
  rcases h₂₃ with ⟨s₂₃, hs₂₃⟩
  refine ⟨s₁₂ ++ s₂₃, ?_⟩
  simpa [List.append_assoc] using hs₂₃

/--
Concrete prefix-freeness for a finite machine domain. Distinct listed codes may not stand
in a proper prefix relation.
-/
def PrefixFreeCodes (codes : List BitCode) : Prop :=
  ∀ ⦃c₁ c₂ : BitCode⦄,
    c₁ ∈ codes →
    c₂ ∈ codes →
    c₁ ≠ c₂ →
    ¬ codeIsPrefix c₁ c₂

/-- Powers of two used in the concrete prefix prior. -/
def pow2 : Nat → Nat
  | 0 => 1
  | n + 1 => 2 * pow2 n

theorem pow2_pos (n : Nat) : 0 < pow2 n := by
  induction n with
  | zero =>
      decide
  | succ n ih =>
      simpa [pow2] using Nat.mul_pos (by decide : 0 < 2) ih

theorem pow2_ne_zero (n : Nat) : pow2 n ≠ 0 :=
  Nat.ne_of_gt (pow2_pos n)

theorem pow2_add (m n : Nat) : pow2 (m + n) = pow2 m * pow2 n := by
  induction n with
  | zero =>
      simp [pow2]
  | succ n ih =>
      calc
        pow2 (m + (n + 1)) = 2 * pow2 (m + n) := by simp [pow2]
        _ = 2 * (pow2 m * pow2 n) := by rw [ih]
        _ = pow2 m * (2 * pow2 n) := by
          simp [Nat.mul_assoc, Nat.mul_comm]
        _ = pow2 m * pow2 (n + 1) := by simp [pow2]

/--
Concrete prefix prior weight of a single codeword. Later phases can normalize or compare
these weights more aggressively; this phase only needs the actual concrete assignment.
-/
def codeWeight (c : BitCode) : Rat :=
  Rat.divInt 1 (pow2 c.length)

/-- Concrete prefix-machine with an explicit finite domain and concrete semantics. -/
structure ConcretePrefixMachine (A : Type u) (O : Type v) where
  codes : List BitCode
  prefixFree : PrefixFreeCodes codes
  semantics : (c : BitCode) → c ∈ codes → ConcreteProgram A O

namespace ConcretePrefixMachine

variable {A : Type u} {O : Type v}

/-- Concrete machine programs are exactly codes in the machine domain. -/
abbrev Program (U : ConcretePrefixMachine A O) := { c : BitCode // c ∈ U.codes }

/-- The raw code underlying a concrete machine program. -/
def programCode (U : ConcretePrefixMachine A O) (p : U.Program) : BitCode :=
  p.1

/-- The concrete interaction semantics attached to a machine program. -/
def programSemantics (U : ConcretePrefixMachine A O) (p : U.Program) :
    ConcreteProgram A O :=
  U.semantics p.1 p.2

/-- Concrete universal prior on machine-domain programs. -/
def universalPrior (U : ConcretePrefixMachine A O) (p : U.Program) : Rat :=
  codeWeight p.1

theorem programCode_mem (U : ConcretePrefixMachine A O) (p : U.Program) :
    U.programCode p ∈ U.codes :=
  p.2

/-- Interaction-prefix semimeasure induced by a concrete machine under a fixed policy. -/
def machineMixture (U : ConcretePrefixMachine A O)
    [DecidableEq A] [DecidableEq O] [BEq A] [LawfulBEq A] [BEq O] [LawfulBEq O]
    (π : ConcretePolicy A O) (t : Nat) (h : Hist A O t) : Rat :=
  listWeightedSum U.codes (fun c =>
    if hc : c ∈ U.codes then
      codeWeight c * (histLaw π (U.semantics c hc) t).mass h
    else
      0)

/--
Prior mass of a concrete machine class, represented as a predicate on machine-domain
programs.
-/
def classPriorMass (U : ConcretePrefixMachine A O)
    (C : U.Program → Prop) [DecidablePred C] : Rat :=
  listWeightedSum U.codes (fun c =>
    if hc : c ∈ U.codes then
      if C ⟨c, hc⟩ then codeWeight c else 0
    else
      0)

/--
Concrete semantic-complexity scaffold: the minimum code length of a class when the class
is nonempty, and `none` otherwise.
-/
def semanticComplexity? (U : ConcretePrefixMachine A O)
    (C : U.Program → Prop) [DecidablePred C] : Option Nat :=
  let lengths :=
    U.codes.foldr
      (fun c acc =>
        if hc : c ∈ U.codes then
          if C ⟨c, hc⟩ then c.length :: acc else acc
        else
          acc)
      []
  match lengths with
  | [] => none
  | n :: ns => some (ns.foldl Nat.min n)

/-- Prefix-extension of one concrete machine inside another by a fixed header code. -/
structure PrefixExtension (U V : ConcretePrefixMachine A O) where
  header : BitCode
  translated_mem :
    ∀ ⦃c : BitCode⦄, c ∈ V.codes → header ++ c ∈ U.codes
  translated_semantics :
    ∀ ⦃c : BitCode⦄ (hc : c ∈ V.codes),
      U.semantics (header ++ c) (translated_mem hc) = V.semantics c hc

/-- The translated code carried by a prefix extension. -/
def PrefixExtension.translateCode {U V : ConcretePrefixMachine A O}
    (E : PrefixExtension U V) (c : BitCode) : BitCode :=
  E.header ++ c

theorem PrefixExtension.translateCode_length {U V : ConcretePrefixMachine A O}
    (E : PrefixExtension U V) (c : BitCode) :
    (E.translateCode c).length = E.header.length + c.length := by
  simp [PrefixExtension.translateCode]

theorem PrefixExtension.translatedPrior_formula {U V : ConcretePrefixMachine A O}
    (E : PrefixExtension U V) (p : V.Program) :
    codeWeight (E.translateCode p.1) = Rat.divInt 1 (pow2 (E.header.length + p.1.length)) := by
  simp [codeWeight, PrefixExtension.translateCode_length]

end ConcretePrefixMachine

end

end AlgorithmicFreeEnergy
