module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.AnyCT
public import VerifiedGarbage.Proof.HashFns.X86_64.WitnessC
import VerifiedGarbage.Proof.Framework.SigEval

/-!
# Deterministic ECDSA on x86-64, for any hash function: `Verified`

`any_verified`: `vg_ecdsa_<curve>_rfc6979_sign` meets the shared contract,
`signAnyContract` under `abi.withConsts` of the comb's tables with 408 bytes
of stack, from `any_correct` and `any_ct`, and the contract can hold
(`any_sat`): in `satAny`, with SHA-1 (`hash = 1`) and the witnesses'
streaming functions (`Witness.C.tableOf_one`), the comb's tables at
`0x100000` held by the memory `m` the curve gives.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86_64

open VG VG.X86_64

/-- A state satisfying the precondition, for scalars of `Q` bytes and the
memory `m` at `0x100000` and above, where every static is: `out` at
`0x1000`, `d` at `0x2000`, a SHA-1 digest at `0x3000`, `scratch` at `0x8000`,
the table at `0x6000` of the witnesses' streaming functions, and its address
the stack argument at `0x20008`. -/
def satAny (Q : Nat) (cs : List (String × List (BitVec 64))) (m : Mem) : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x3000 | .rcx => 20 | .r8 => 0x8000 | .r9 => 1
    | .rsp => 0x20000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := bif Nat.beq a.toNat 0x20009 then 0x60 else bif Nat.beq a.toNat 0x6001 then 0x70
    else bif Nat.beq a.toNat 0x6009 then 0x71 else bif Nat.beq a.toNat 0x6011 then 0x72
    else bif Nat.ble 0x100000 a.toNat then m a else 0
  rd := [⟨0x2000, Q⟩, ⟨0x3000, 20⟩, ⟨0x6000, 24⟩, ⟨0x20008, 8⟩] ++ Abi.constRegions (fun _ => 0x100000) cs
  wr := [⟨0x1000, 2 * Q⟩, ⟨0x8000, 8192⟩]
  syms _ := 0x100000
  funs := HashFns.X86_64.Witness.funs

theorem satAny_mem {Q : Nat} {cs : List (String × List (BitVec 64))} {m : Mem} {x : Addr}
    (h : 0x100000 ≤ x.toNat) : (satAny Q cs m).mem x = m x := by
  have h₁ : Nat.beq x.toNat 0x20009 = false := Bool.eq_false_iff.mpr fun e => by
    have := Nat.eq_of_beq_eq_true e; omega
  have h₂ : Nat.beq x.toNat 0x6001 = false := Bool.eq_false_iff.mpr fun e => by
    have := Nat.eq_of_beq_eq_true e; omega
  have h₃ : Nat.beq x.toNat 0x6009 = false := Bool.eq_false_iff.mpr fun e => by
    have := Nat.eq_of_beq_eq_true e; omega
  have h₄ : Nat.beq x.toNat 0x6011 = false := Bool.eq_false_iff.mpr fun e => by
    have := Nat.eq_of_beq_eq_true e; omega
  have h₅ : Nat.ble 0x100000 x.toNat = true := Nat.ble_eq.mpr h
  simp only [satAny, h₁, h₂, h₃, h₄, h₅, Bool.cond_false, Bool.cond_true]

/-- Below `0x100000`, the memory of `satAny` is that of the closed state
`satAny 0 [] 0`, which the kernel evaluates. -/
theorem satAny_low {Q : Nat} {cs : List (String × List (BitVec 64))} {m : Mem} {x : Addr}
    (h : x.toNat < 0x100000) : (satAny Q cs m).mem x = (satAny 0 [] fun _ => 0).mem x := by
  have h₅ : Nat.ble 0x100000 x.toNat = false := Bool.eq_false_iff.mpr fun e => by
    have := Nat.le_of_ble_eq_true e; omega
  simp only [satAny, h₅, Bool.cond_false]

theorem satAny_readW {Q : Nat} {cs : List (String × List (BitVec 64))} {m : Mem} {a : Addr} {w : Nat}
    (h : ∀ i < w / 8, (a + BitVec.ofNat 64 i).toNat < 0x100000) :
    (satAny Q cs m).mem.readW a w = (satAny 0 [] fun _ => 0).mem.readW a w :=
  Mem.readW_congr fun i hi => satAny_low (h i hi)

theorem sep_of {b₁ b₂ : Addr} {l₁ l₂ : Nat} (h₁ : b₁.toNat + l₁ ≤ 2 ^ 64) (h₂ : b₂.toNat + l₂ ≤ 2 ^ 64)
    (h : b₁.toNat + l₁ ≤ b₂.toNat ∨ b₂.toNat + l₂ ≤ b₁.toNat) : Region.Disjoint ⟨b₁, l₁⟩ ⟨b₂, l₂⟩ :=
  Region.disjoint_of_sep (by
    simp only [Region.sep, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]; exact ⟨⟨h₁, h₂⟩, h⟩)

namespace RfcAny

variable (A : RfcAny)

theorem len72 : A.I.ecdsa.curve.len ≤ 72 := by
  rw [A.ecdsa, A.R.curve]; have := A.R.len_words; have := A.R.n9; omega

/-- The shared contract can hold, with the comb's tables at `0x100000` in
`m`, which they fit above. -/
theorem any_sat (m : Mem) (held : Abi.constsHeld m (fun _ => 0x100000) A.cs)
    (hlen : ∀ c ∈ A.cs, 0x100000 + 8 * c.2.length ≤ 2 ^ 64) :
    ∃ s, (A.I.signAnyContract (abi.withConsts A.cs) 408).pre s := by
  have hQ := A.len72
  refine ⟨satAny A.I.ecdsa.curve.len A.cs m, pre_of_apre ?_⟩
  have ha : stackArgAddr (satAny A.I.ecdsa.curve.len A.cs m) 0 = 0x20008 := rfl
  have hsa : stackArg (satAny A.I.ecdsa.curve.len A.cs m) 0 = 0x6000 := by
    unfold stackArg; rw [ha]; exact (satAny_readW (by decide)).trans (by decide)
  have hsw : A.I.scratchWords * 8 = 8192 := by rw [A.scratch]
  have hT : ∀ t ∈ Abi.constRegions (fun _ => (0x100000 : Addr)) A.cs, t.base.toNat = 0x100000 ∧
      0x100000 + t.len ≤ 2 ^ 64 := fun t ht => by
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ht
    exact ⟨rfl, hlen c hc⟩
  have hdT : ∀ t ∈ Abi.constRegions (fun _ => (0x100000 : Addr)) A.cs, ∀ (b : Addr) (l : Nat),
      b.toNat + l ≤ 0x100000 → t.Disjoint ⟨b, l⟩ := fun t ht b l hb => by
    obtain ⟨e, hl⟩ := hT t ht
    exact sep_of (by omega) (by omega) (.inr (by omega))
  have h9 : ((satAny A.I.ecdsa.curve.len A.cs m).gpr .r9).toNat = 1 := rfl
  have hsp : ((satAny A.I.ecdsa.curve.len A.cs m).gpr .rsp).toNat = 0x20000 := rfl
  have hO : outR A.I (satAny A.I.ecdsa.curve.len A.cs m) = ⟨0x1000, 2 * A.I.ecdsa.curve.len⟩ := rfl
  have hD : dR A.I (satAny A.I.ecdsa.curve.len A.cs m) = ⟨0x2000, A.I.ecdsa.curve.len⟩ := rfl
  have hG : dgR (satAny A.I.ecdsa.curve.len A.cs m) = ⟨0x3000, 20⟩ := rfl
  have hS : scrR A.I (satAny A.I.ecdsa.curve.len A.cs m) = ⟨0x8000, 8192⟩ := by simp only [scrR, hsw]; rfl
  have hTb : tabR (satAny A.I.ecdsa.curve.len A.cs m) = ⟨0x6000, 24⟩ := by simp only [tabR, hsa]
  have hA : argR (satAny A.I.ecdsa.curve.len A.cs m) = ⟨0x20008, 8⟩ := by simp only [argR, ha]
  have hR : retR (satAny A.I.ecdsa.curve.len A.cs m) = ⟨0x20000, 8⟩ := rfl
  have hK : stkR (satAny A.I.ecdsa.curve.len A.cs m) = ⟨130664, 408⟩ := by
    show (⟨(0x20000 : Addr) - BitVec.ofNat 64 408, 408⟩ : Region) = _
    rw [show (0x20000 : Addr) - BitVec.ofNat 64 408 = 130664 by decide]
  refine ⟨by rw [hsp]; decide, by rw [hsp]; decide, ?rd, ?held, ?tbl, ?wr,
    by rw [hO, hD]; exact sep_of (by simp <;> omega) (by simp <;> omega) (by simp <;> omega),
    by rw [hO, hG]; exact sep_of (by simp <;> omega) (by simp <;> omega) (by simp <;> omega),
    by rw [hO, hS]; exact sep_of (by simp <;> omega) (by simp <;> omega) (by simp <;> omega),
    by rw [hO, hTb]; exact sep_of (by simp <;> omega) (by simp <;> omega) (by simp <;> omega),
    by rw [hO, hA]; exact sep_of (by simp <;> omega) (by simp <;> omega) (by simp <;> omega),
    by rw [hD, hS]; exact sep_of (by simp <;> omega) (by simp <;> omega) (by simp <;> omega),
    by rw [hG, hS]; exact sep_of (by simp <;> omega) (by simp <;> omega) (by simp <;> omega),
    by rw [hS, hTb]; exact sep_of (by simp <;> omega) (by simp <;> omega) (by simp <;> omega),
    by rw [hS, hA]; exact sep_of (by simp <;> omega) (by simp <;> omega) (by simp <;> omega),
    by rw [hR, hO]; exact sep_of (by simp <;> omega) (by simp <;> omega) (by simp <;> omega),
    by rw [hR, hD]; exact sep_of (by simp <;> omega) (by simp <;> omega) (by simp <;> omega),
    by rw [hR, hG]; exact sep_of (by simp <;> omega) (by simp <;> omega) (by simp <;> omega),
    by rw [hR, hS]; exact sep_of (by simp <;> omega) (by simp <;> omega) (by simp <;> omega),
    by rw [hR, hTb]; exact sep_of (by simp <;> omega) (by simp <;> omega) (by simp <;> omega),
    by rw [hR, hA]; exact sep_of (by simp <;> omega) (by simp <;> omega) (by simp <;> omega),
    by rw [hK, hO]; exact sep_of (by simp <;> omega) (by simp <;> omega) (by simp <;> omega),
    by rw [hK, hD]; exact sep_of (by simp <;> omega) (by simp <;> omega) (by simp <;> omega),
    by rw [hK, hG]; exact sep_of (by simp <;> omega) (by simp <;> omega) (by simp <;> omega),
    by rw [hK, hS]; exact sep_of (by simp <;> omega) (by simp <;> omega) (by simp <;> omega),
    by rw [hK, hTb]; exact sep_of (by simp <;> omega) (by simp <;> omega) (by simp <;> omega),
    by rw [hK, hA]; exact sep_of (by simp <;> omega) (by simp <;> omega) (by simp <;> omega),
    by show (0x1000 : Addr).toNat + _ ≤ _; simp <;> omega,
    by show (0x2000 : Addr).toNat + _ ≤ _; simp <;> omega,
    by show (0x3000 : Addr).toNat + (20 : Addr).toNat ≤ _; decide,
    by show (0x8000 : Addr).toNat + _ ≤ _; rw [hsw]; decide,
    by rw [hsa]; decide, ?hk, ?dl, ?fns⟩
  case rd => simp only [tabR, hsa]; rfl
  case wr => simp only [outR, scrR, hsw]; rfl
  case held =>
    refine constsHeld_congr held (fun t ht => by have := hT t ht; omega) fun t ht x hx => satAny_mem ?_
    obtain ⟨e, hl⟩ := hT t ht
    simp only [Region.Contains, BitVec.toNat_sub, e] at hx
    omega
  case tbl =>
    intro t ht
    refine ⟨by have := hT t ht; omega, fun r hr => ?_, by rw [hR]; exact hdT t ht _ _ (by decide),
      by rw [hK]; exact hdT t ht _ _ (by decide)⟩
    simp only [satAny, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hdT t ht _ _ (by simp; omega)
    · exact hdT t ht _ _ (by decide)
  case fns =>
    rw [h9, hsa]
    exact HashFns.X86_64.Witness.C.tableOf_one (a₀ := 0x7000) (a₁ := 0x7100) (a₂ := 0x7200) rfl rfl rfl
      ((satAny_readW (by decide)).trans (by decide)) ((satAny_readW (by decide)).trans (by decide))
      ((satAny_readW (by decide)).trans (by decide))
  case hk => rw [h9]; decide
  case dl =>
    intro H hH
    rw [h9] at hH
    cases hH
    rfl

/-- `vg_ecdsa_<curve>_rfc6979_sign` meets the shared contract, with the comb's
tables at `0x100000` in `m`, which they fit above (for `any_sat`). -/
theorem any_verified (m : Mem) (held : Abi.constsHeld m (fun _ => 0x100000) A.cs)
    (hlen : ∀ c ∈ A.cs, 0x100000 + 8 * c.2.length ≤ 2 ^ 64) :
    Verified X86_64.target A.code (A.I.signAnyContract (X86_64.abi.withConsts A.cs) 408) :=
  Verified.of_correct A.any_correct A.any_ct (Contract.Implies.refl (A.any_sat m held hlen))

end RfcAny

/-- The notes on the implementation, for the documentation of the function
whose candidates `core` signs with. -/
def anyNotes (core : String) : String :=
  "Moves the addresses in the table `hash_fns` to `r9`, `r10` and `r11`, and chooses, by comparing `hash` \
  with each number, the code for that hash function's sizes, which calls them through `r11`: HMAC's inner and \
  outer streaming states, its working space and its messages are in `scratch`. Unless the scalars are longer \
  than the hash, `h = bits2octets(digest)` is a conditional subtraction of `n` from the digest's leftmost bytes, \
  a word at a time; otherwise `h` is zero bytes and the digest, and each candidate the leftmost bits of \
  successive `V`s, shifted in place. Each candidate `k` is tried with `" ++ core ++ "`, which uses all of \
  `scratch`; whether to try another is computed without branches from its result and the count of candidates \
  left, so the code branches only on that and on `hash`. `K`, `V`, `h`, the count, the pointers and the \
  addresses are kept in a 384-byte stack frame, whose secrets are cleared before it is popped; the calls use \
  the 24 bytes below it."

end VG.Proof.Ecdsa.Rfc6979.X86_64
