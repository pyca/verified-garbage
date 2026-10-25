module

public import VerifiedGarbage.Proof.MlKem.X86_64.SHTop
public import VerifiedGarbage.Proof.MlKem.X86_64.PrfBatch
import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Sha3.X86_64.Permute

/-!
# ML-KEM on x86-64: `Sample4.sampleP`, two outputs of `PRF₂` in the fourth state

`sampleP` (`Impl/MlKem/X86_64/SampleH.lean`) samples three entries of the
matrix as `sampleHM fast 0` does, while the fourth state computes
`PRF₂(σ, 0)` and `PRF₂(σ, 1)`. Before each of the first two squeezes its
lanes are those of the padded block of `σ ‖ N` (`pload_ok`, with
`Prf4.P0`, the state `PrfBatch.lean`'s four-way `PRF₂` permutes), and after
it the first 128 bytes of the permuted state are copied out (`pext_ok`).

The contract (`samplePKW`): `vg_mlkem_sample_ntt4`'s precondition and public
data, and as postcondition its result and polynomials for the first three
seeds (`Post3`) and the two outputs at `scratch + oPO`, of `σ` at
`scratch + oPS`.
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (keccakF bytesAt)

/-- The contract of `Sample4.sampleP`. -/
def samplePKW : Contract isa where
  pre := (sample4KW true).pre
  post s s' := SH.Post3 true s s' ∧ ∀ N < 2,
    bytesAt s'.mem (s.gpr .rdx + BitVec.ofNat 64 (Impl.MlKem.X86_64.Sample4.oPO + 128 * N)) 128 =
      prf 2 (bytesAt s.mem (s.gpr .rdx + BitVec.ofNat 64 Impl.MlKem.X86_64.Sample4.oPS) 32) (BitVec.ofNat 8 N)
  pub := sample4K.pub

namespace SH

open VG.Impl.MlKem.X86_64.Sample4
open VG.Proof.MlKem.X86_64.S4
open VG.Proof.Sha3 (byteOf byteOf_eq iterF)
open VG.Proof.Sha3.X86_64.X4 (la lane_ext)
open VG.Proof.MlKem.X86_64.Prf4 (P0 byteOf_P0 bytes_prf)

/-! ## The padded block, lane by lane -/

/-- Lane `j` of the padded block of `σ ‖ N`, with `σ` at `p` and lane 4 `v`. -/
def PV (m : Mem) (p : Addr) (v : BitVec 64) (j : Nat) : BitVec 64 :=
  if j < 4 then m.readW (p + BitVec.ofNat 64 (8 * j)) 64 else if j = 4 then v
  else if j = 16 then 0x8000000000000000#64 else 0

theorem PF_hi {σ : List Byte} {n : Byte} {q : Nat} (hq : 34 ≤ q) : Prf4.PF σ n q = if q = 135 then 0x80 else 0 := by
  unfold Prf4.PF
  rw [ifn (by omega_arith), ifn (by omega_arith), ifn (by omega_arith)]

theorem lane4_byte {N : Nat} (hN : N < 256) {b : Nat} (hb : b < 8) :
    (BitVec.ofNat 64 (0x1f00 + N)).extractLsb' (8 * b) 8 =
      if b = 0 then BitVec.ofNat 8 N else if b = 1 then 0x1f else 0 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat]
  rcases (by omega_arith : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 ∨ b = 5 ∨ b = 6 ∨ b = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp <;> omega_arith

theorem lane16_byte : ∀ b < 8, (0x8000000000000000#64).extractLsb' (8 * b) 8 = if b = 7 then 0x80 else 0 := by
  decide

/-- Lane `j` of `Prf4.P0`: of `σ` in memory, of the index and suffix, of the
padding's last byte, and zero. -/
theorem P0_lane {m : Mem} {p : Addr} {N : Nat} (hN : N < 256) {j : Nat} (hj : j < 25) :
    (P0 (bytesAt m p 32) (BitVec.ofNat 8 N))[j]! = PV m p (BitVec.ofNat 64 (0x1f00 + N)) j := by
  have hl : (bytesAt m p 32).length = 32 := VG.Proof.MlKem.bytesAt_length _ _ _
  refine lane_ext fun b hb => ?_
  have e := byteOf_eq (P0 (bytesAt m p 32) (BitVec.ofNat 8 N)) hj hb
  rw [byteOf_P0 hl _ (by omega_arith)] at e
  rw [VG.Proof.Sha3.getElem!_eq _ hj, ← e]
  unfold PV
  by_cases h4 : j < 4
  · rw [ifp h4, byte_readW _ _ (by omega_arith), Offset.add_add, Prf4.PF, ifp (by omega_arith),
      VG.Proof.MlKem.bytesAt_getD _ _ (by omega_arith)]
  · rw [ifn h4]
    by_cases e4 : j = 4
    · subst e4
      rw [ifp rfl, lane4_byte hN hb, Prf4.PF, ifn (by omega_arith)]
      rcases (by omega_arith : b = 0 ∨ b = 1 ∨ 2 ≤ b) with rfl | rfl | h2
      · rw [ifp rfl, ifp rfl]
      · rw [ifn (show ¬ 8 * 4 + 1 = 32 by decide), ifp (show 8 * 4 + 1 = 33 by decide), ifn (by decide), ifp rfl]
      · rw [ifn (by omega_arith), ifn (by omega_arith), ifn (by omega_arith), ifn (by omega_arith), ifn (by omega_arith)]
    · rw [ifn e4, PF_hi (by omega_arith)]
      by_cases e16 : j = 16
      · subst e16
        rw [ifp rfl, lane16_byte b hb]
        by_cases e7 : b = 7
        · subst e7; rfl
        · rw [ifn e7, ifn (by omega_arith)]
      · rw [ifn e16, ifn (by omega_arith)]
        exact (BitVec.extractLsb'_zero ..).symm

/-! ## The fourth state overwritten -/

section
variable {w16 : Bool}

/-- The four states. -/
abbrev stR (σ : State) : Region := ⟨scr σ, 800⟩

/-- During `pload`, from `s₀`: the first `i` lanes of the fourth state are `V`'s. -/
structure PLI (σ s₀ : State) (V : Nat → BitVec 64) (i : Nat) (s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  gpr : ∀ r, r ≠ .rax → s.gpr r = s₀.gpr r
  fr : Frame [stR σ] s₀.mem s.mem
  w : ∀ j < 25, ∀ k < 4, s.mem.readW (la (scr σ) j k) 64 =
    if k = 3 ∧ j < i then V j else s₀.mem.readW (la (scr σ) j k) 64

/-- Lane `j` of the fourth state stored, with `V j`. -/
theorem PLI.store {σ s₀ : State} {V : Nat → BitVec 64} {j : Nat} (hj : j < 25) {s s₂ : State}
    (h : PLI σ s₀ V j s) {v : BitVec 64} (hv : v = V j) (hm : s₂.mem = s.mem.writeW (at' σ (32 * j + 24)) v)
    (hrd : s₂.rd = s.rd) (hwr : s₂.wr = s.wr) (hg : ∀ r, r ≠ .rax → s₂.gpr r = s.gpr r) : PLI σ s₀ V (j + 1) s₂ := by
  have hf : Frame [⟨at' σ (32 * j + 24), 8⟩] s.mem s₂.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine ⟨hrd.trans h.rd, hwr.trans h.wr, fun r hr => (hg r hr).trans (h.gpr r hr),
    h.fr.trans (hf.sub fun r hr => ⟨stR σ, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub_base _ (by omega_arith)⟩), fun i hi k hk => ?_⟩
  rw [hm]
  by_cases e : i = j ∧ k = 3
  · obtain ⟨rfl, rfl⟩ := e
    rw [show la (scr σ) i 3 = at' σ (32 * i + 24) from rfl, Mem.readW_writeW_self64, ite_eq_left ⟨rfl, by omega_arith⟩, hv]
  · have e' := readW_writeW_off s.mem (scr σ) v (d := 32 * i + 8 * k) (e := 32 * j + 24) (n := 8) (by omega_arith) (by omega_arith)
      (by omega_arith)
    rw [show la (scr σ) i k = scr σ + BitVec.ofNat 64 (32 * i + 8 * k) from rfl, e', ← la, h.w i hi k hk]
    by_cases c : k = 3 ∧ i < j
    · rw [ite_eq_left c, ite_eq_left ⟨c.1, by omega_arith⟩]
    · rw [ite_eq_right c, ite_eq_right (by omega_arith)]

/-- The lanes `pload` stores, from `s₀`: `PV` of `σ` at `scratch + oPS` and `r9`. -/
abbrev PVs (σ s₀ : State) : Nat → BitVec 64 := PV s₀.mem (at' σ oPS) (s₀.gpr .r9)

open VG.Proof.Sha3.X86_64 (wp_movm wp_store wp_movi64 wp_mov32i wp_nil) in
theorem plane_ok {σ : State} (hp : PreW w16 σ) {s₀ : State} (he : EnvW w16 σ s₀) {j : Nat} (hj : j < 25) {s : State}
    (h : PLI σ s₀ (PVs σ s₀) j s) : WP isa (.block (plane j)) s (PLI σ s₀ (PVs σ s₀) (j + 1)) := by
  have hrd : s.rd = σ.rd := h.rd.trans he.rd
  have hwr : s.wr = σ.wr := h.wr.trans he.wr
  have hbx : s.gpr .rbx = scr σ := (h.gpr _ (by decide)).trans he.rbx
  have hst : InRegions s.wr (at' σ (32 * j + 24)) 8 := in_scr hp hwr (by omega_arith)
  have hea : s.ea (at_ .rbx (32 * j + 24)) = at' σ (32 * j + 24) := by rw [ea_at, hbx]
  unfold plane
  by_cases h4 : j < 4
  · rw [ifp h4]
    refine wp_movm (a := at' σ (oPS + 8 * j)) (by rw [ea_at, hbx]) (in_scr' hp hrd hwr (by simp only [oPS]; omega_arith))
      fun s₁ u₁ => wp_store (a := at' σ (32 * j + 24)) (by rw [ea_at, u₁.other _ (by decide), hbx])
        (by rw [u₁.wr]; exact hst) fun s₂ g₂ m₂ r₂ w₂ => wp_nil ?_
    refine h.store hj ?_ (by rw [m₂, u₁.mem, u₁.gpr]) (r₂.trans u₁.rd) (w₂.trans u₁.wr)
      fun r hr => by rw [g₂, u₁.other r hr]
    rw [PVs, PV, ifp h4, at', Offset.add_add]
    exact h.fr.readW (Region.contains_self _ _) (by
      simpa using Offset.disjoint_base (scr σ) (k := 800) (d := oPS + 8 * j) (n := 8) (by simp only [oPS]; omega_arith)
        (by simp only [oPS]; omega_arith)) (by decide)
  · rw [ifn h4]
    by_cases e4 : j = 4
    · subst e4
      rw [ifp rfl]
      refine wp_store (a := at' σ (32 * 4 + 24)) hea hst fun s₂ g₂ m₂ r₂ w₂ => wp_nil ?_
      refine h.store hj ?_ m₂ r₂ w₂ fun r _ => by rw [g₂]
      rw [PVs, PV, ifn (by decide), ifp rfl, h.gpr _ (by decide)]
    · rw [ifn e4]
      by_cases e16 : j = 16
      · subst e16
        rw [ifp rfl]
        refine wp_movi64 fun s₁ u₁ => wp_store (a := at' σ (32 * 16 + 24)) (by rw [ea_at, u₁.other _ (by decide), hbx])
          (by rw [u₁.wr]; exact hst) fun s₂ g₂ m₂ r₂ w₂ => wp_nil ?_
        refine h.store hj (v := 0x8000000000000000#64) ?_ (by rw [m₂, u₁.mem, u₁.gpr]) (r₂.trans u₁.rd)
          (w₂.trans u₁.wr) fun r hr => by rw [g₂, u₁.other r hr]
        rw [PVs, PV, ifn (by decide), ifn (by decide), ifp rfl]
      · rw [ifn e16]
        refine wp_mov32i fun s₁ u₁ => wp_store (a := at' σ (32 * j + 24)) (by rw [ea_at, u₁.other _ (by decide), hbx])
          (by rw [u₁.wr]; exact hst) fun s₂ g₂ m₂ r₂ w₂ => wp_nil ?_
        refine h.store hj (v := 0) ?_ (by rw [m₂, u₁.mem, u₁.gpr]; rfl) (r₂.trans u₁.rd)
          (w₂.trans u₁.wr) fun r hr => by rw [g₂, u₁.other r hr]
        rw [PVs, PV, ifn h4, ifn e4, ifn e16]

/-- The fourth state overwritten with the padded block of `σ ‖ N`, for `N` in
`r9` (with SHAKE's suffix): it writes only the four states. -/
theorem pload_ok {σ : State} (hp : PreW w16 σ) {Y : Spec.Sha3.State} {t n : Nat} {s : State}
    (h : SqY w16 σ Y t n s) (hn : n ≤ 3) {N : Nat} (hN : N < 256) (h9 : s.gpr .r9 = BitVec.ofNat 64 (0x1f00 + N)) :
    WP isa (.block pload) s fun s' => SqY w16 σ (P0 (bytesAt s.mem (at' σ oPS) 32) (BitVec.ofNat 8 N)) t n s' ∧
      Frame [stR σ] s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ ∀ r, r ≠ .rax → s'.gpr r = s.gpr r := by
  refine WP.mono (wp_range_flatMap (M := isa) (PLI σ s (PVs σ s)) (fun i t hi ht => plane_ok hp h.env hi ht) 25
    (Nat.le_refl _) s ⟨rfl, rfl, fun _ _ => rfl, Frame.refl _ _, fun j _ k _ => by rw [ite_eq_right (by omega_arith)]⟩)
    fun s' h' => ⟨?_, h'.fr, h'.rd, h'.wr, h'.gpr⟩
  have hsub : ∀ r ∈ [stR σ], Region.Sub r ⟨scr σ, oSave⟩ := fun r hr => by
    rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by simp only [oSave]; omega_arith)
  refine ⟨EnvW.low h.env hsub h'.fr h'.rd h'.wr fun r hr => h'.gpr r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide),
    by rw [h'.gpr _ (by decide), h.r14], fun r hr k hk => ?_, fun j hj k hk => ?_, fun k hk p hp' => ?_⟩
  · rw [h'.fr.readW (Region.contains_self _ _) (by
      simpa using Offset.disjoint_base (scr σ) (k := 800) (d := 32 * (50 + r) + 8 * k) (n := 8) (by omega_arith) (by omega_arith))
      (by decide)]
    exact h.rc r hr k hk
  · rw [h'.w j hj k hk]
    by_cases e : k = 3
    · subst e
      rw [ite_eq_left ⟨rfl, hj⟩, L3_three, PVs, h9, P0_lane hN hj]
    · rw [ite_eq_right (by omega_arith), h.lanes j hj k hk, L3_lt (by omega_arith), L3_lt (by omega_arith)]
  · rw [h'.fr (at' σ (oBuf + 504 * k + p)) fun r hr hc => by
      rw [List.mem_singleton.mp hr] at hc
      exact (Offset.disjoint_base (scr σ) (k := 800) (d := oBuf + 504 * k + p) (n := 1) (by simp only [oBuf]; omega_arith)
        (by simp only [oBuf]; omega_arith)) _ (Region.contains_self _ _) hc]
    exact h.buf k hk p hp'

end

/-! ## The output copied out -/

section
variable {w16 : Bool}

/-- During `pext`, from `s₀`, to `o`: the first `i` lanes of the fourth state copied. -/
structure PXI (σ s₀ : State) (o : Nat) (i : Nat) (s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  gpr : ∀ r, r ≠ .rax → s.gpr r = s₀.gpr r
  fr : Frame [⟨at' σ o, 128⟩] s₀.mem s.mem
  out : ∀ l < i, s.mem.readW (at' σ (o + 8 * l)) 64 = s₀.mem.readW (la (scr σ) l 3) 64

open VG.Proof.Sha3.X86_64 (wp_movm wp_store wp_nil) in
theorem pext_step {σ : State} (hp : PreW w16 σ) {s₀ : State} (he : EnvW w16 σ s₀) {o : Nat} (ho : 800 ≤ o)
    (ho' : o + 128 ≤ 8192) (h8 : s₀.gpr .r8 = at' σ o) {i : Nat} (hi : i < 16) {s : State} (h : PXI σ s₀ o i s) :
    WP isa (.block [.mov .rax (.mem (at_ .rbx (32 * i + 24))), .store (at_ .r8 (8 * i)) .rax]) s
      (PXI σ s₀ o (i + 1)) := by
  have hrd : s.rd = σ.rd := h.rd.trans he.rd
  have hwr : s.wr = σ.wr := h.wr.trans he.wr
  have hbx : s.gpr .rbx = scr σ := (h.gpr _ (by decide)).trans he.rbx
  have hr8 : s.gpr .r8 = at' σ o := (h.gpr _ (by decide)).trans h8
  refine wp_movm (a := at' σ (32 * i + 24)) (by rw [ea_at, hbx]) (in_scr' hp hrd hwr (by omega_arith)) fun s₁ u₁ =>
    wp_store (a := at' σ (o + 8 * i)) (by rw [ea_at, u₁.other _ (by decide), hr8, at', at', Offset.add_add])
      (by rw [u₁.wr]; exact in_scr hp hwr (by omega_arith)) fun s₂ g₂ m₂ r₂ w₂ => wp_nil ?_
  have hv : s.mem.readW (at' σ (32 * i + 24)) 64 = s₀.mem.readW (la (scr σ) i 3) 64 :=
    h.fr.readW (Region.contains_self _ _) (by
      simpa using Offset.disjoint (scr σ) (d := 32 * i + 24) (n := 8) (e := o) (k := 128) (.inl (by omega_arith)) (by omega_arith)
        (by omega_arith)) (by decide)
  have hm : s₂.mem = s.mem.writeW (at' σ (o + 8 * i)) (s₀.mem.readW (la (scr σ) i 3) 64) := by
    rw [m₂, u₁.mem, u₁.gpr, hv]
  have hf : Frame [⟨at' σ (o + 8 * i), 8⟩] s.mem s₂.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine ⟨(r₂.trans u₁.rd).trans h.rd, (w₂.trans u₁.wr).trans h.wr, fun r hr => by rw [g₂, u₁.other r hr, h.gpr r hr],
    h.fr.trans (hf.sub fun r hr => ⟨⟨at' σ o, 128⟩, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub _ (by omega_arith) (by omega_arith)⟩), fun l hl => ?_⟩
  rw [hm]
  by_cases e : l = i
  · subst e; exact Mem.readW_writeW_self64 _ _ _
  · rw [rd64_off (by omega_arith) (by omega_arith) (by omega_arith)]
    exact h.out l (by omega_arith)

theorem pext_eq : pext = (List.range 16).flatMap (fun i => [.mov .rax (.mem (at_ .rbx (32 * i + 24))),
    .store (at_ .r8 (8 * i)) .rax]) ++ ([.alu .add .r8 (.imm 128), .alu .add .r9 (.imm 1)] : List Instr) := rfl

open VG.Proof.Sha3.X86_64 (wp_addi wp_nil) in
/-- The first 128 bytes of the fourth state `Z` to `r8`, and `r8` and `r9` to the next. -/
theorem pext_ok {σ : State} (hp : PreW w16 σ) {Z : Spec.Sha3.State} {t n : Nat} {s : State} (h : SqY w16 σ Z t n s)
    (hn : n ≤ 3) {o : Nat} (ho : 800 ≤ o) (ho' : o + 128 ≤ 8192) (ho₁ : oSave + 40 ≤ o) (h8 : s.gpr .r8 = at' σ o) :
    WP isa (.block pext) s fun s' => SqY w16 σ Z t n s' ∧ Frame [⟨at' σ o, 128⟩] s.mem s'.mem ∧
      (∀ j < 128, s'.mem (at' σ o + BitVec.ofNat 64 j) = byteOf Z j) ∧ s'.gpr .r8 = at' σ (o + 128) ∧
      s'.gpr .r9 = s.gpr .r9 + 1 ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      ∀ r, r ≠ .rax → r ≠ .r8 → r ≠ .r9 → s'.gpr r = s.gpr r := by
  rw [pext_eq, WP.block_append_iff]
  refine WP.mono (wp_range_flatMap (M := isa) (PXI σ s o) (fun i t hi ht => pext_step hp h.env ho ho' h8 hi ht) 16
    (Nat.le_refl _) s ⟨rfl, rfl, fun _ _ => rfl, Frame.refl _ _, fun _ h => absurd h (by omega_arith)⟩)
    fun t ht => wp_addi fun t₁ u₁ => wp_addi fun t₂ u₂ => wp_nil ?_
  have hm : t₂.mem = t.mem := u₂.mem.trans u₁.mem
  have hg : ∀ r, r ≠ .rax → r ≠ .r8 → r ≠ .r9 → t₂.gpr r = s.gpr r := fun r h₁ h₂ h₃ => by
    rw [u₂.other r h₃, u₁.other r h₂, ht.gpr r h₁]
  have hf : Frame [⟨at' σ o, 128⟩] s.mem t₂.mem := by rw [hm]; exact ht.fr
  refine ⟨h.apart hn hf (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Offset.base_disjoint _ (by simp only [oSave] at ho₁ ⊢; omega_arith) (by omega_arith))
    (fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact Offset.disjoint _ (.inl (by simp only [oSave] at ho₁ ⊢; omega_arith)) (by simp only [oSave]; omega_arith) (by omega_arith))
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact ⟨scrR σ, by simp, sub_scr (by omega_arith)⟩)
    (u₂.rd.trans (u₁.rd.trans ht.rd)) (u₂.wr.trans (u₁.wr.trans ht.wr)) fun r hr => hg r
      (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with h | h | h | h | h | h <;> simp [h])
      (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with h | h | h | h | h | h <;> simp [h])
      (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with h | h | h | h | h | h <;> simp [h]),
    hf, fun j hj => ?_, ?_, ?_, u₂.rd.trans (u₁.rd.trans ht.rd), u₂.wr.trans (u₁.wr.trans ht.wr), hg⟩
  · rw [hm]
    have hl := h.lanes (j / 8) (by omega_arith) 3 (by decide)
    rw [L3_three, VG.Proof.Sha3.getElem!_eq _ (show j / 8 < 25 by omega_arith)] at hl
    have e := (ht.out (j / 8) (by omega_arith)).trans hl
    have b := congrArg (BitVec.extractLsb' (8 * (j % 8)) 8) e
    rw [byte_readW _ _ (by omega_arith), at', Offset.add_add, show o + 8 * (j / 8) + j % 8 = o + j by omega_arith,
      ← Offset.add_add, ← at'] at b
    have be := byteOf_eq Z (show j / 8 < 25 by omega_arith) (show j % 8 < 8 by omega_arith)
    rw [show 8 * (j / 8) + j % 8 = j by omega_arith] at be
    rw [b, be]
  · rw [u₂.other _ (by decide), u₁.gpr, ht.gpr _ (by decide), h8, at', at',
      show (128 : BitVec 32).signExtend 64 = BitVec.ofNat 64 128 from rfl, Offset.add_add]
  · rw [u₂.gpr, u₁.other _ (by decide), ht.gpr _ (by decide)]; rfl

end

/-! ## The two squeezes with `PRF₂`, and the third -/

section
variable {w16 : Bool}

/-- `squeeze`, keeping `r9` too. -/
theorem sqYg_ok {fast : Bool} {σ : State} (hp : PreW w16 σ) {Y : Spec.Sha3.State} {t n : Nat} (hn : n < 3) {s : State}
    (h : SqY w16 σ Y t n s) (hbp : s.gpr .rbp = at' σ (oBuf + 168 * n)) :
    WP isa (squeeze fast) s fun s' => (SqY w16 σ (keccakF Y) t (n + 1) s' ∧ Frame [lowR σ] s.mem s'.mem) ∧
      s'.gpr .rbp = s.gpr .rbp ∧ s'.gpr .r10 = s.gpr .r10 ∧ s'.gpr .r8 = s.gpr .r8 ∧ s'.gpr .r9 = s.gpr .r9 := by
  unfold squeeze
  exact permY_ok (fast := fast) hp hn h fun s' ⟨he, h14, hrc, hl, hb, hf, h₁, h₂, hg⟩ =>
    WP.mono (WP.keep [.rax] (extractY_ok hp hn ⟨he, h14, hrc, hl, fun k hk p _ hc => hb k hk p (by omega_arith), hf,
      by rw [h₁, hbp]⟩) (by decide)) fun s'' ⟨h', k⟩ =>
        ⟨h', by rw [k.gpr (by decide), h₁], by rw [k.gpr (by decide), h₂],
          by rw [k.gpr (by decide), hg _ (by decide) (by decide) (by decide) (by decide) (by decide)],
          by rw [k.gpr (by decide), hg _ (by decide) (by decide) (by decide) (by decide) (by decide)]⟩

/-- `σ` at entry. -/
abbrev sigB (σ : State) : List Byte := bytesAt σ.mem (at' σ oPS) 32

/-- The fourth state after `i` of the squeezes with `PRF₂`. -/
def Yp (σ : State) : Nat → Spec.Sha3.State
  | 0 => A0 (B σ 3)
  | i + 1 => keccakF (P0 (sigB σ) (BitVec.ofNat 8 i))

/-- Output `N` of `PRF₂`. -/
abbrev poA (σ : State) (N : Nat) : Addr := at' σ (oPO + 128 * N)

/-- After `i` of the squeezes with `PRF₂`. -/
structure PI (w16 : Bool) (σ : State) (i : Nat) (t : State) : Prop where
  sq : SqY w16 σ (Yp σ i) 0 i t
  hr : HR σ t.mem
  r8 : t.gpr .r8 = poA σ i
  r9 : t.gpr .r9 = BitVec.ofNat 64 (0x1f00 + i)
  out : ∀ N < i, bytesAt t.mem (poA σ N) 128 = prf 2 (sigB σ) (BitVec.ofNat 8 N)

/-- `σ` in the sponge's blocks, as at entry. -/
theorem HR.sig {σ : State} {m : Mem} (h : HR σ m) : bytesAt m (at' σ oPS) 32 = sigB σ :=
  VG.Proof.MlKem.bytesAt_congr fun k hk => by
    rw [at', Offset.add_add, show oPS + k = oHS + (200 + k) by simp only [oPS, oHS]; omega_arith, ← at']
    exact h _ (by omega_arith)

/-- A region of the scratch space from `oSave + 40` on, apart from the sponge's state and blocks. -/
theorem hR_apart (σ : State) {d n : Nat} (h : oHS + 608 ≤ d) (h' : d + n ≤ 8192) :
    (hR σ).Disjoint ⟨at' σ d, n⟩ :=
  Offset.disjoint _ (.inl (by simp only [oHS] at h ⊢; omega_arith)) (by simp only [oHS]; omega_arith) (by omega_arith)

theorem squeezeP_ok {fast : Bool} {σ : State} (hp : PreW w16 σ) {i : Nat} (hi : i < 2) {t : State} (h : PI w16 σ i t)
    (hbp : t.gpr .rbp = at' σ (oBuf + 168 * i)) :
    WP isa (squeezeP fast) t fun t' => PI w16 σ (i + 1) t' ∧ t'.gpr .rbp = t.gpr .rbp ∧ t'.gpr .r10 = t.gpr .r10 := by
  unfold squeezeP
  refine WP.seq (WP.mono (pload_ok hp h.sq (by omega_arith) (N := i) (by omega_arith) h.r9) fun t₁ ⟨q₁, f₁, rd₁, wr₁, g₁⟩ => ?_)
  rw [h.hr.sig] at q₁
  have hd₁ : ∀ {d n : Nat}, 800 ≤ d → d + n ≤ 8192 → (stR σ).Disjoint ⟨at' σ d, n⟩ := fun hd hn =>
    Offset.base_disjoint _ hd (by omega_arith)
  refine WP.seq (WP.mono (sqYg_ok (fast := fast) hp (by omega_arith) q₁ (by rw [g₁ _ (by decide), hbp])) fun t₂ ⟨⟨q₂, f₂⟩, bp₂, r10₂, r8₂, r9₂⟩ => ?_)
  refine WP.mono (pext_ok hp q₂ (by omega_arith) (o := oPO + 128 * i) (by simp only [oPO]; omega_arith) (by simp only [oPO]; omega_arith)
    (by simp only [oPO, oSave]; omega_arith) (by rw [r8₂, g₁ _ (by decide), h.r8])) fun t₃ ⟨q₃, f₃, b₃, r8₃, r9₃, _, _, g₃⟩ => ?_
  have hlow : ∀ {d n : Nat}, oSave ≤ d → d + n ≤ 8192 → (lowR σ).Disjoint ⟨at' σ d, n⟩ := fun hd hn =>
    Offset.base_disjoint _ hd (by simp only [oSave] at hd ⊢; omega_arith)
  refine ⟨⟨q₃, ((h.hr.frame f₁ fun r hr => by
        rw [List.mem_singleton.mp hr]; exact (hd₁ (d := oHS) (n := 608) (by simp only [oHS]; omega_arith) (by simp only [oHS]; omega_arith)).symm).frame f₂
      fun r hr => by rw [List.mem_singleton.mp hr]; exact (hlow (d := oHS) (n := 608) (by simp only [oHS, oSave]; omega_arith) (by simp only [oHS]; omega_arith)).symm).frame f₃
      fun r hr => by rw [List.mem_singleton.mp hr]; exact hR_apart σ (by simp only [oPO, oHS]; omega_arith) (by simp only [oPO]; omega_arith),
    by rw [r8₃, poA, show oPO + 128 * i + 128 = oPO + 128 * (i + 1) by omega_arith],
    by rw [r9₃, r9₂, g₁ _ (by decide), h.r9, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, BitVec.ofNat_add_ofNat,
      Nat.add_assoc], fun N hN => ?_⟩, ?_, ?_⟩
  · rcases (by omega_arith : N < i ∨ N = i) with hN' | rfl
    · rw [VG.Proof.MlKem.bytesAt_frame f₃ (fun r hr => by
          rw [List.mem_singleton.mp hr]
          exact Offset.disjoint _ (.inl (by omega_arith)) (by simp only [oPO]; omega_arith) (by simp only [oPO]; omega_arith)) (by decide),
        VG.Proof.MlKem.bytesAt_frame f₂ (fun r hr => by
          rw [List.mem_singleton.mp hr]; exact (hlow (by simp only [oPO, oSave]; omega_arith) (by simp only [oPO]; omega_arith)).symm) (by decide),
        VG.Proof.MlKem.bytesAt_frame f₁ (fun r hr => by
          rw [List.mem_singleton.mp hr]; exact (hd₁ (by simp only [oPO]; omega_arith) (by simp only [oPO]; omega_arith)).symm) (by decide)]
      exact h.out N hN'
    · exact bytes_prf (VG.Proof.MlKem.bytesAt_length _ _ _) fun j hj => b₃ j hj
  · rw [g₃ _ (by decide) (by decide) (by decide), bp₂, g₁ _ (by decide)]
  · rw [g₃ _ (by decide) (by decide) (by decide), r10₂, g₁ _ (by decide)]

end

/-! ## The fragment -/

section

/-- The two outputs of `PRF₂`. -/
def HP (σ : State) (m : Mem) : Prop := ∀ N < 2, bytesAt m (poA σ N) 128 = prf 2 (sigB σ) (BitVec.ofNat 8 N)

theorem HP.stab (σ : State) : Stab σ (HP σ) := fun {m m' rs} h hf hd N hN => by
  have hs : Region.Sub ⟨poA σ N, 128⟩ (hkR σ) :=
    Offset.sub (scr σ) (d := oPO + 128 * N) (n := 128) (e := oHS) (k := 1472) (by simp only [oPO, oHS]; omega_arith)
      (by simp only [oPO, oHS]; omega_arith)
  rw [VG.Proof.MlKem.bytesAt_frame hf (fun r hr => (hd r hr).sub_left hs) (by decide)]
  exact h N hN

open VG.Proof.Sha3.X86_64 (wp_mov wp_addi wp_mov32i wp_nil) in
/-- The prologue, the round constants, the padded seeds, and `r8` and `r9`. -/
theorem startP_ok {σ : State} (hp : PreW true σ) :
    WP isa (.block (pro ++ Impl.Sha3.X86_64.X4.rcTable .rbx (oRc / 32) ++ absorb4 ++
      ([.mov .r8 (.reg .rbx), .alu .add .r8 (.imm (BitVec.ofNat 32 oPO)), .mov32 .r9 (.imm 0x1f00)] : List Instr))) σ
      (PI true σ 0) := by
  rw [show ∀ (a b c d : List Instr), a ++ b ++ c ++ d = (a ++ b ++ c) ++ d from fun _ _ _ _ => by
    simp only [List.append_assoc], WP.block_append_iff]
  refine WP.mono (startF_ok hp) fun s₁ ⟨h₁, r₁⟩ => wp_mov fun s₂ u₂ => wp_addi fun s₃ u₃ => wp_mov32i fun s₄ u₄ =>
    wp_nil ?_
  have hm : s₄.mem = s₁.mem := u₄.mem.trans (u₃.mem.trans u₂.mem)
  have k : Keep [.r8, .r9] s₁ s₄ := ⟨fun r hr => by
      rw [u₄.other r (by simp at hr; exact hr.2), u₃.other r (by simp at hr; exact hr.1),
        u₂.other r (by simp at hr; exact hr.1)],
    u₄.rd.trans (u₃.rd.trans u₂.rd), u₄.wr.trans (u₃.wr.trans u₂.wr)⟩
  refine ⟨⟨h₁.env.keep hm k (by decide), by rw [k.gpr (by decide), h₁.r14], by rw [hm]; exact h₁.rc,
      fun j hj c hc => ?_, fun _ _ p hp' => absurd hp' (by omega_arith)⟩, by rw [hm]; exact r₁, ?_, ?_,
    fun _ hN => absurd hN (by omega_arith)⟩
  · rw [hm, h₁.lanes j hj c hc]
    by_cases e : c < 3
    · rw [L3_lt e]
    · rw [show c = 3 by omega_arith, L3_three]; rfl
  · rw [u₄.other _ (by decide), u₃.gpr, u₂.gpr, h₁.env.rbx, poA, at', sx_ofNat (by simp only [oPO]; omega_arith), Nat.mul_zero,
      Nat.add_zero]
  · rw [u₄.gpr]; rfl

/-- The two squeezes with `PRF₂`, from the start. -/
theorem squeezesP_ok {fast : Bool} {σ : State} (hp : PreW true σ) {s : State} (h : PI true σ 0 s) :
    WP isa (blocks oBuf 168 2 (squeezeP fast)) s (PI true σ 2) := by
  have hbx : s.gpr .rbx = scr σ := h.sq.env.rbx
  exact blocks_ok (b := 0) (P := PI true σ) (by decide) (by decide) (by simp only [oBuf]; omega_arith) (by decide)
    (fun _ _ _ h' hm hrd hwr hg => ⟨h'.sq.frame hm hrd hwr hg, by rw [hm]; exact h'.hr,
      by rw [hg _ (by decide) (by decide)]; exact h'.r8, by rw [hg _ (by decide) (by decide)]; exact h'.r9,
      by rw [hm]; exact h'.out⟩)
    (fun i t _ hi hI hbp => squeezeP_ok (fast := fast) hp (by omega_arith) hI (by
      rw [hbp, hbx, at', Offset.add_add, Nat.sub_zero])) h

theorem correctP {fast : Bool} (σ : State) (hs : samplePKW.pre σ) :
    ∃ t s', Exec isa (sampleP fast) σ t s' ∧ abiPreserved σ s' ∧ samplePKW.post σ s' := by
  have hp := preW_of (w16 := true) hs
  have hlow : (lowR σ).Disjoint (hkR σ) := low_hs σ
  obtain ⟨t, s', he, hF⟩ := WP.seq (WP.mono (startP_ok hp) fun s₁ h₁ =>
    WP.seq (WP.mono (squeezesP_ok (fast := fast) hp h₁) fun s₂ h₂ =>
      WP.seq (WP.mono (sqYs_ok (fast := fast) hp (b := 2) (n := 1) (by decide) (by decide) h₂.sq) fun s₃ ⟨h₃, f₃⟩ =>
        run3G_ok (fast := fast) (H := HP σ) hp h₃ (HP.stab σ h₂.out f₃ fun r hr => by
          rw [List.mem_singleton.mp hr]; exact hlow.symm) (HP.stab σ))))
  refine ⟨t, s', he, abiPreserved_of_exec (by cases fast <;> decide +kernel) he hF.2.2, hF.1, hF.2.1⟩

end

end SH

end VG.Proof.MlKem.X86_64
