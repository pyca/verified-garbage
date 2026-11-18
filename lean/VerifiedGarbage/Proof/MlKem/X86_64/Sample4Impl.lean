module

public import VerifiedGarbage.Proof.MlKem.X86_64.S4Verified16
public import VerifiedGarbage.Proof.MlKem.X86_64.SHCT
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.MlKem.X86_64.SHTop
public import VerifiedGarbage.Proof.MlKem.X86_64.FragPrim
public import VerifiedGarbage.Proof.MlKem.X86_64.Prfs
import VerifiedGarbage.Proof.MlKem.X86_64.YLanes
public import VerifiedGarbage.Proof.Bignum.X86_64.Loop
public import VerifiedGarbage.Proof.Framework.Range
public import VerifiedGarbage.Proof.MlKem.X86_64.Cbd
public import VerifiedGarbage.Proof.MlKem.X86_64.Decode12
public import VerifiedGarbage.Proof.MlKem.X86_64.Decode12Avx2
public import VerifiedGarbage.Proof.MlKem.X86_64.DecodeDecompress
public import VerifiedGarbage.Proof.MlKem.X86_64.Encode12
public import VerifiedGarbage.Proof.MlKem.X86_64.Lit
public import VerifiedGarbage.Proof.MlKem.X86_64.NttR.Top
public import VerifiedGarbage.Proof.MlKem.X86_64.YNttPack
public import VerifiedGarbage.Proof.MlKem.X86_64.KpkeAcc
public import VerifiedGarbage.Proof.MlKem.X86_64.WritesOnly
public import VerifiedGarbage.Proof.MlKem.X86_64.FinY
public import VerifiedGarbage.Proof.MlKem.X86_64.Zero
public import VerifiedGarbage.Proof.Poly1305.Limbs64
public import VerifiedGarbage.Proof.Sha3.X86_64.Stream.Pad
public import VerifiedGarbage.Proof.Framework.TacticTemplate
public meta import VerifiedGarbage.Proof.Framework.TacticTemplate
import VerifiedGarbage.Proof.MlKem.X86_64.S4Top
public import VerifiedGarbage.Proof.Framework.X86_64.InstrBits
public import VerifiedGarbage.Proof.MlKem.X86_64.S4CT
import VerifiedGarbage.Proof.MlKem.X86_64.S4Verified
meta import VerifiedGarbage.Proof.MlKem.X86_64.S4Verified
meta import VerifiedGarbage.Proof.MlKem.X86_64.S4Top
import VerifiedGarbage.Proof.MlKem.Bits
meta import VerifiedGarbage.Proof.MlKem.Bits
import VerifiedGarbage.Impl.MlKem.X86_64.Frag
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Framework.X86_64.Words
import VerifiedGarbage.Proof.MlKem.Encode
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.MlKem.X86_64.FragCall
meta import VerifiedGarbage.Impl.MlKem.X86_64.Frag
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Bitslice.Lanes
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.WriteBytes
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.X86_64.Sse
meta import VerifiedGarbage.Proof.Framework.X86_64.Words
meta import VerifiedGarbage.Proof.MlKem.Compress
meta import VerifiedGarbage.Proof.MlKem.Encode
meta import VerifiedGarbage.Proof.MlKem.Mem
meta import VerifiedGarbage.Proof.MlKem.X86_64.Bytes
meta import VerifiedGarbage.Proof.MlKem.X86_64.FragCall
meta import VerifiedGarbage.Proof.MlKem.X86_64.S4CT
meta import VerifiedGarbage.Proof.MlKem.X86_64.S4Tab
meta import VerifiedGarbage.Proof.MlKem.X86_64.YLanes
meta import VerifiedGarbage.Proof.Sha3.X86_64.Stream.Pad
meta import VerifiedGarbage.Proof.Sha3.X86_64.X4R.Loop
meta import VerifiedGarbage.Proof.MlKem.X86_64.SHCT
meta import VerifiedGarbage.Proof.MlKem.X86_64.SHTop
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Framework.TaintBatch
public import VerifiedGarbage.Proof.MlKem.X86_64.PrfBatch
import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Sha3.X86_64.Permute
meta import VerifiedGarbage.Proof.MlKem.X86_64.PrfBatch
meta import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.Framework.X86_64.Avx
meta import VerifiedGarbage.Proof.Sha3.X86_64.Permute

/-! ### `MlKem.X86_64.SHPCT`, which only this module used -/

section

/-! ### `MlKem.X86_64.SHP`, which this module and modules that import it used -/

section

/-!
# ML-KEM on x86-64: `Sample4.samplePN`, outputs of `PRF₂` in the fourth state

`samplePN fast N₀ m` (`Impl/MlKem/X86_64/SampleH.lean`) samples three
entries of the matrix as `sampleHM fast 0` does, while the fourth state
computes `PRF₂(σ, N₀)`, …, `PRF₂(σ, N₀ + m - 1)`, for `0 < m ≤ 3`. Before
each of the first `m` squeezes its lanes are those of the padded block of
`σ ‖ N` (`pload_ok`, with `Prf4.P0`, the state `PrfBatch.lean`'s four-way
`PRF₂` permutes), and after it the first 128 bytes of the permuted state are
copied out (`pext_ok`).

The contract (`samplePNKW N₀ m`): `vg_mlkem_sample_ntt4`'s precondition and
public data, and as postcondition its result and polynomials for the first
three seeds (`Post3`) and the `m` outputs at `scratch + oPO`, of `σ` at
`scratch + oPS`.
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (keccakF bytesAt)

/-- The contract of `Sample4.samplePN fast N₀ m`. -/
def samplePNKW (N₀ m : Nat) : Contract isa where
  pre := (sample4KW true).pre
  post s s' := SH.Post3 true s s' ∧ ∀ N < m,
    bytesAt s'.mem (s.gpr .rdx + BitVec.ofNat 64 (Impl.MlKem.X86_64.Sample4.oPO + 128 * N)) 128 =
      prf 2 (bytesAt s.mem (s.gpr .rdx + BitVec.ofNat 64 Impl.MlKem.X86_64.Sample4.oPS) 32) (BitVec.ofNat 8 (N₀ + N))
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

/-- The fourth state after `i` of the squeezes with `PRF₂`, from `PRF₂(σ, N₀)`. -/
def Yp (σ : State) (N₀ : Nat) : Nat → Spec.Sha3.State
  | 0 => A0 (B σ 3)
  | i + 1 => keccakF (P0 (sigB σ) (BitVec.ofNat 8 (N₀ + i)))

/-- Output `N` of `PRF₂`. -/
abbrev poA (σ : State) (N : Nat) : Addr := at' σ (oPO + 128 * N)

/-- After `i` of the squeezes with `PRF₂`, from `PRF₂(σ, N₀)`. -/
structure PI (w16 : Bool) (σ : State) (N₀ i : Nat) (t : State) : Prop where
  sq : SqY w16 σ (Yp σ N₀ i) 0 i t
  hr : HR σ t.mem
  r8 : t.gpr .r8 = poA σ i
  r9 : t.gpr .r9 = BitVec.ofNat 64 (0x1f00 + N₀ + i)
  out : ∀ N < i, bytesAt t.mem (poA σ N) 128 = prf 2 (sigB σ) (BitVec.ofNat 8 (N₀ + N))

/-- `σ` in the sponge's blocks, as at entry. -/
theorem HR.sig {σ : State} {m : Mem} (h : HR σ m) : bytesAt m (at' σ oPS) 32 = sigB σ :=
  VG.Proof.MlKem.bytesAt_congr fun k hk => by
    rw [at', Offset.add_add, show oPS + k = oHS + (200 + k) by simp only [oPS, oHS]; omega_arith, ← at']
    exact h _ (by omega_arith)

/-- A region of the scratch space from `oSave + 40` on, apart from the sponge's state and blocks. -/
theorem hR_apart (σ : State) {d n : Nat} (h : oHS + 608 ≤ d) (h' : d + n ≤ 8192) :
    (hR σ).Disjoint ⟨at' σ d, n⟩ :=
  Offset.disjoint _ (.inl (by simp only [oHS] at h ⊢; omega_arith)) (by simp only [oHS]; omega_arith) (by omega_arith)

theorem squeezeP_ok {fast : Bool} {σ : State} (hp : PreW w16 σ) {N₀ i : Nat} (hi : i < 3) (hN : N₀ + i < 256) {t : State}
    (h : PI w16 σ N₀ i t) (hbp : t.gpr .rbp = at' σ (oBuf + 168 * i)) :
    WP isa (squeezeP fast) t fun t' => PI w16 σ N₀ (i + 1) t' ∧ t'.gpr .rbp = t.gpr .rbp ∧ t'.gpr .r10 = t.gpr .r10 := by
  unfold squeezeP
  refine WP.seq (WP.mono (pload_ok hp h.sq (by omega_arith) (N := N₀ + i) hN (by rw [h.r9, Nat.add_assoc]))
    fun t₁ ⟨q₁, f₁, rd₁, wr₁, g₁⟩ => ?_)
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
      congrArg (BitVec.ofNat 64) (show 0x1f00 + N₀ + i + 1 = 0x1f00 + N₀ + (i + 1) by omega_arith)], fun N hN => ?_⟩, ?_, ?_⟩
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

/-- The `m ≤ 3` outputs of `PRF₂`, from `PRF₂(σ, N₀)`. -/
def HP (σ : State) (N₀ m : Nat) (M : Mem) : Prop :=
  ∀ N < m, bytesAt M (poA σ N) 128 = prf 2 (sigB σ) (BitVec.ofNat 8 (N₀ + N))

theorem HP.stab (σ : State) {N₀ m : Nat} (hm : m ≤ 3) : Stab σ (HP σ N₀ m) := fun {M M' rs} h hf hd N hN => by
  have hs : Region.Sub ⟨poA σ N, 128⟩ (hkR σ) :=
    Offset.sub (scr σ) (d := oPO + 128 * N) (n := 128) (e := oHS) (k := 1472) (by simp only [oPO, oHS]; omega_arith)
      (by simp only [oPO, oHS]; omega_arith)
  rw [VG.Proof.MlKem.bytesAt_frame hf (fun r hr => (hd r hr).sub_left hs) (by decide)]
  exact h N hN

open VG.Proof.Sha3.X86_64 (wp_mov wp_addi wp_mov32i wp_nil) in
/-- The prologue, the round constants, the padded seeds, and `r8` and `r9`. -/
theorem startP_ok {σ : State} (hp : PreW true σ) {N₀ : Nat} (hN : N₀ < 256) :
    WP isa (.block (pro ++ Impl.Sha3.X86_64.X4.rcTable .rbx (oRc / 32) ++ absorb4 ++
      ([.mov .r8 (.reg .rbx), .alu .add .r8 (.imm (BitVec.ofNat 32 oPO)),
        .mov32 .r9 (.imm (BitVec.ofNat 32 (0x1f00 + N₀)))] : List Instr))) σ
      (PI true σ N₀ 0) := by
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
  · rw [u₄.gpr, Nat.add_zero]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega_arith

/-- The `m` squeezes with `PRF₂`, from the start. -/
theorem squeezesP_ok {fast : Bool} {σ : State} (hp : PreW true σ) {N₀ m : Nat} (hm : 0 < m) (hm' : m ≤ 3)
    (hN : N₀ + m ≤ 256) {s : State} (h : PI true σ N₀ 0 s) :
    WP isa (blocks oBuf 168 m (squeezeP fast)) s (PI true σ N₀ m) := by
  have hbx : s.gpr .rbx = scr σ := h.sq.env.rbx
  refine WP.mono (blocks_ok (start := oBuf) (step := 168) (b := 0) (n := m) (P := PI true σ N₀) hm (by omega_arith) (by simp only [oBuf]; omega_arith) (by decide)
    (fun _ _ _ h' hm hrd hwr hg => ⟨h'.sq.frame hm hrd hwr hg, by rw [hm]; exact h'.hr,
      by rw [hg _ (by decide) (by decide)]; exact h'.r8, by rw [hg _ (by decide) (by decide)]; exact h'.r9,
      by rw [hm]; exact h'.out⟩)
    (fun i t _ hi hI hbp => squeezeP_ok (fast := fast) hp (by omega_arith) (by omega_arith) hI (by
      rw [hbp, hbx, at', Offset.add_add, Nat.sub_zero])) h) fun _ h => by rwa [Nat.zero_add] at h

/-- The squeezes after the `m` with `PRF₂`. -/
theorem restP_ok {fast : Bool} {σ : State} (hp : PreW true σ) {N₀ m : Nat} (hm' : m ≤ 3) {s : State}
    (h : PI true σ N₀ m s) :
    WP isa (if m = 3 then .block [] else squeezes m (3 - m) fast) s fun s' =>
      SqY true σ (iterF (3 - m) (Yp σ N₀ m)) 0 3 s' ∧ HP σ N₀ m s'.mem := by
  by_cases e : m = 3
  · subst e
    rw [ifp rfl]
    exact VG.Proof.Sha3.X86_64.wp_nil ⟨h.sq, h.out⟩
  · rw [ifn e]
    refine WP.mono (sqYs_ok (fast := fast) hp (b := m) (n := 3 - m) (by omega_arith) (by omega_arith) h.sq)
      fun s' ⟨h', f'⟩ => ⟨by rwa [show m + (3 - m) = 3 by omega_arith] at h', HP.stab σ hm' h.out f' fun r hr => by
        rw [List.mem_singleton.mp hr]; exact (low_hs σ).symm⟩

theorem correctPN {fast : Bool} {N₀ m : Nat} (hm : 0 < m) (hm' : m ≤ 3) (hN : N₀ + m ≤ 256)
    (hc : (samplePN fast N₀ m).allInstrs (fun i => !loadsMxcsr i) = true) (σ : State)
    (hs : (samplePNKW N₀ m).pre σ) :
    ∃ t s', Exec isa (samplePN fast N₀ m) σ t s' ∧ abiPreserved σ s' ∧ (samplePNKW N₀ m).post σ s' := by
  have hp := preW_of (w16 := true) hs
  unfold samplePN at hc ⊢
  rw [ifn (show ¬ m = 0 by omega_arith)] at hc ⊢
  obtain ⟨t, s', he, hF⟩ := WP.seq (WP.mono (startP_ok hp (N₀ := N₀) (by omega_arith)) fun s₁ h₁ =>
    WP.seq (WP.mono (squeezesP_ok (fast := fast) hp hm hm' hN h₁) fun s₂ h₂ =>
      WP.seq (WP.mono (restP_ok (fast := fast) hp hm' h₂) fun s₃ ⟨h₃, f₃⟩ =>
        run3G_ok (fast := fast) (H := HP σ N₀ m) hp h₃ f₃ (HP.stab σ hm'))))
  exact ⟨t, s', he, abiPreserved_of_exec hc he hF.2.2, hF.1, hF.2.1⟩

end

end SH

end VG.Proof.MlKem.X86_64

end

end

/-!
# ML-KEM on x86-64: `Sample4.samplePN`, constant time but for the seeds

As `sampleH` (`SHCT.lean`): the code but for the loops and the checks of the
counts is proven by the taint analysis from the pointers, with every byte
of the states secret. `σ`, which the fourth state absorbs, flows only into
the states, the fourth buffer and the outputs of `PRF₂`, at fixed addresses;
the loops of both runs read the same output of the first three seeds.
`ctPN` takes the taint analysis of the parts that depend on `N₀` and `m`,
which the kernel evaluates for each of `Sample4.pnUses` (`ctPN_uses`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64.SH

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlKem.X86_64.Sample4
open VG.Proof.MlKem.X86_64.S4
open VG.Proof.Sha3 (iterF)

/-- The start. -/
theorem startP_ct {N₀ : Nat} (hN : N₀ < 256) {hc : VG.Taint.Hint X86_64.Taint.T}
    (c : (taint.check (X86_64.Taint.ofRegs [.rdi, .rsi, .rdx])
      (.block (pro ++ Impl.Sha3.X86_64.X4.rcTable .rbx (oRc / 32) ++ absorb4 ++
        ([.mov .r8 (.reg .rbx), .alu .add .r8 (.imm (BitVec.ofNat 32 oPO)),
          .mov32 .r9 (.imm (BitVec.ofNat 32 (0x1f00 + N₀)))] : List Instr))) hc).isSome = true) :
    RelCT isa (S4.R4W true fun σ s => s = σ)
    (.block (pro ++ Impl.Sha3.X86_64.X4.rcTable .rbx (oRc / 32) ++ absorb4 ++
      ([.mov .r8 (.reg .rbx), .alu .add .r8 (.imm (BitVec.ofNat 32 oPO)),
        .mov32 .r9 (.imm (BitVec.ofNat 32 (0x1f00 + N₀)))] : List Instr)))
    (S4.R4W true fun σ s => PI true σ N₀ 0 s) :=
  relInv (fun σ s hp h => by subst h; exact startP_ok (preW_of hp) hN)
    (taintRel [.rdi, .rsi, .rdx] (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
      subst h₁ h₂
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      exacts [hq.1, hq.2.1, hq.2.2.1]) c)

/-- The `m` squeezes with `PRF₂`. -/
theorem sqP_ct {fast : Bool} {N₀ m : Nat} (hm : 0 < m) (hm' : m ≤ 3) (hN : N₀ + m ≤ 256)
    {hc : VG.Taint.Hint X86_64.Taint.T}
    (c : (taint.check (X86_64.Taint.ofRegs [.rbx, .r8]) (blocks oBuf 168 m (squeezeP fast)) hc).isSome = true) :
    RelCT isa (S4.R4W true fun σ s => PI true σ N₀ 0 s) (blocks oBuf 168 m (squeezeP fast))
      (S4.R4W true fun σ s => PI true σ N₀ m s) :=
  relInv (fun σ s hp h => squeezesP_ok (fast := fast) (preW_of hp) hm hm' hN h)
    (taintRel [.rbx, .r8] (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
      have hb := env_rbx hq h₁.sq.env h₂.sq.env
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hb
      · rw [h₁.r8, h₂.r8, poA, poA, at', at', ← h₁.sq.env.rbx, ← h₂.sq.env.rbx, hb]) c)

/-- The squeezes after them. -/
theorem sq3P_ct {fast : Bool} {N₀ m : Nat} (hm' : m ≤ 3) {hc : VG.Taint.Hint X86_64.Taint.T}
    (c : (taint.check (X86_64.Taint.ofRegs [.rbx]) (if m = 3 then .block [] else squeezes m (3 - m) fast) hc).isSome = true) :
    RelCT isa (S4.R4W true fun σ s => PI true σ N₀ m s) (if m = 3 then .block [] else squeezes m (3 - m) fast)
      (S4.R4W true fun σ s => SqY true σ (iterF (3 - m) (Yp σ N₀ m)) 0 3 s ∧ HP σ N₀ m s.mem) :=
  relInv (fun σ s hp h => restP_ok (fast := fast) (preW_of hp) hm' h)
    (taintRel [.rbx] (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact env_rbx hq h₁.sq.env h₂.sq.env) c)

theorem ctPN {fast : Bool} {N₀ m : Nat} (hm : 0 < m) (hm' : m ≤ 3) (hN : N₀ + m ≤ 256)
    {h₁ : VG.Taint.Hint X86_64.Taint.T}
    (c₁ : (taint.check (X86_64.Taint.ofRegs [.rdi, .rsi, .rdx])
      (.block (pro ++ Impl.Sha3.X86_64.X4.rcTable .rbx (oRc / 32) ++ absorb4 ++
        ([.mov .r8 (.reg .rbx), .alu .add .r8 (.imm (BitVec.ofNat 32 oPO)),
          .mov32 .r9 (.imm (BitVec.ofNat 32 (0x1f00 + N₀)))] : List Instr))) h₁).isSome = true)
    {h₂ : VG.Taint.Hint X86_64.Taint.T}
    (c₂ : (taint.check (X86_64.Taint.ofRegs [.rbx, .r8]) (blocks oBuf 168 m (squeezeP fast)) h₂).isSome = true)
    {h₃ : VG.Taint.Hint X86_64.Taint.T}
    (c₃ : (taint.check (X86_64.Taint.ofRegs [.rbx]) (if m = 3 then .block [] else squeezes m (3 - m) fast) h₃).isSome = true) :
    ConstantTime isa (samplePNKW N₀ m).pre (samplePNKW N₀ m).pub (samplePN fast N₀ m) := by
  unfold samplePN
  rw [ifn (show ¬ m = 0 by omega_arith)]
  refine relStart (Q := fun _ _ => True) (RelCT.seq (startP_ct (by omega_arith) c₁) (RelCT.seq (sqP_ct hm hm' hN c₂)
    (RelCT.seq (sq3P_ct hm' c₃)
    (RelCT.seq (tabY_ct (Y := fun σ => iterF (3 - m) (Yp σ N₀ m)) (H := fun σ => HP σ N₀ m) fun σ => HP.stab σ hm') ?_))))
  refine RelCT.seq (run1Y_ct (K := 0) (by decide) (by taint_decide)) ?_
  refine RelCT.seq (run1Y_ct (K := 1) (by decide) (by taint_decide)) ?_
  refine RelCT.seq (run1Y_ct (K := 2) (by decide) (by taint_decide)) ?_
  exact tail3_ct

theorem ctPN_uses {fast : Bool} {q : Nat × Nat} (hq : q ∈ pnUses) :
    ConstantTime isa (samplePNKW q.1 q.2).pre (samplePNKW q.1 q.2).pub (samplePN fast q.1 q.2) := by
  simp only [pnUses, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl <;> cases fast <;>
    refine ctPN (by decide) (by decide) (by decide) (h₁ := ?_) ?_ (h₂ := ?_) ?_ (h₃ := ?_) ?_
  taint_decide_all

end VG.Proof.MlKem.X86_64.SH

end

end

/-! ### `MlKem.X86_64.SHM`, which only this module used -/

section

/-!
# ML-KEM on x86-64: `Sample4.sampleHM`, the sponge absorbing `m` blocks

`sampleH` (`SHTop.lean`, `SHCT.lean`) with the fourth state absorbing only
the first `m ≤ 3` blocks (`squeezesH'_ok`), stored back as the sponge's
after the `m`-th squeeze (`hsave_ok`), then permuted by the other squeezes
(`sqYs_ok`), which write below the sponge's state; the runs on the first
three seeds do not depend on the fourth state.
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64.SH

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlKem.X86_64.Sample4
open VG.Proof.MlKem.X86_64.S4
open VG.Proof.Sha3 (iterF)

/-- The three squeezes, the first `m` absorbing a block, with the sponge's
state stored after the `m`-th. -/
theorem squeezesHM_ok {fast : Bool} {m : Nat} (hm : m ≤ 3) {σ : State} (hp : PreW true σ) {s : State}
    (h : SqY true σ (hst σ 0) 0 0 s) (hr : HR σ s.mem) :
    WP isa (squeezesHM fast m) s fun s' => SqY true σ (iterF (3 - m) (hst σ m)) 0 3 s' ∧ HS σ (hst σ m) s'.mem := by
  unfold squeezesHM
  have h₁ : WP isa (if m = 0 then .block [] else squeezesHM.squeezesH' fast m) s
      fun s' => SqY true σ (hst σ m) 0 m s' := by
    by_cases h0 : m = 0
    · subst h0; rw [ite_eq_left rfl]; exact WP.block_nil h
    · rw [ite_eq_right h0]; exact WP.mono (squeezesH'_ok (by omega_using [h0]) hm hp h hr) fun _ h' => h'.1
  refine WP.seq (WP.mono h₁ fun s₁ q₁ => WP.seq (WP.mono (hsave_ok hp q₁ hm) fun s₂ ⟨q₂, e₂⟩ => ?_))
  by_cases h3 : m = 3
  · subst h3; rw [ite_eq_left rfl]; exact WP.block_nil ⟨q₂, e₂⟩
  · rw [ite_eq_right h3]
    refine WP.mono (sqYs_ok (fast := fast) hp (n := 3 - m) (by omega_using [hm, h3]) (by omega_using [hm]) q₂) fun s' ⟨q', f'⟩ => ?_
    refine ⟨by rwa [show m + (3 - m) = 3 by omega_using [hm]] at q', HS.stab σ _ e₂ f' fun r hr => ?_⟩
    rw [List.mem_singleton.mp hr]; exact (low_hs σ).symm

theorem correctHM {fast : Bool} {m : Nat} (hm : m ≤ 3) (σ : State) (hs : (sampleHMKW true m).pre σ) :
    ∃ t s', Exec isa (sampleHM fast m) σ t s' ∧ abiPreserved σ s' ∧ (sampleHMKW true m).post σ s' := by
  have hp := preW_of (w16 := true) hs
  obtain ⟨t, s', he, hF⟩ := WP.seq (WP.mono (startF_ok hp) fun s₁ ⟨h₁, r₁⟩ =>
    WP.seq (WP.mono (hload_ok hp h₁ r₁) fun s₂ ⟨h₂, r₂⟩ =>
      WP.seq (WP.mono (squeezesHM_ok (fast := fast) hm hp h₂ r₂) fun s₃ ⟨h₃, e₃⟩ =>
        run3_ok (fast := fast) hp h₃ e₃)))
  refine ⟨t, s', he, abiPreserved_of_exec ?_ he hF.2, hF.1⟩
  rcases (by omega_using [hm] : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3) with rfl | rfl | rfl | rfl <;> cases fast <;> decide +kernel

theorem squeezesHM_ct {fast : Bool} {m : Nat} (hm : m ≤ 3) :
    RelCT isa (S4.R4W true fun σ s => SqY true σ (hst σ 0) 0 0 s ∧ HR σ s.mem) (squeezesHM fast m)
      (S4.R4W true fun σ s => SqY true σ (iterF (3 - m) (hst σ m)) 0 3 s ∧ HS σ (hst σ m) s.mem) := by
  have hsq : ∃ hc : VG.Taint.Hint X86_64.Taint.T,
      (taint.check (X86_64.Taint.ofRegs [.rbx]) (squeezesHM fast m) hc).isSome = true := by
    rcases (by omega_using [hm] : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3) with rfl | rfl | rfl | rfl <;> cases fast
    all_goals exact ⟨_, by taint_decide⟩
  obtain ⟨_, c⟩ := hsq
  exact relInv (fun σ s hp h => squeezesHM_ok (fast := fast) hm (preW_of hp) h.1 h.2)
    (taintRel [.rbx] (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact env_rbx hq h₁.1.env h₂.1.env) c)

theorem ctHM {fast : Bool} {m : Nat} (hm : m ≤ 3) :
    ConstantTime isa (sampleHMKW true m).pre (sampleHMKW true m).pub (sampleHM fast m) := by
  refine relStart (Q := fun _ _ => True) (RelCT.seq startH_ct (RelCT.seq hload_ct
    (RelCT.seq (squeezesHM_ct (fast := fast) hm)
      (RelCT.seq (tabY_ct (Y := fun σ => iterF (3 - m) (hst σ m)) (H := fun σ => HS σ (hst σ m)) fun σ => HS.stab σ _) ?_))))
  refine RelCT.seq (run1Y_ct (K := 0) (by decide) (by taint_decide)) ?_
  refine RelCT.seq (run1Y_ct (K := 1) (by decide) (by taint_decide)) ?_
  refine RelCT.seq (run1Y_ct (K := 2) (by decide) (by taint_decide)) ?_
  exact tail3_ct

end VG.Proof.MlKem.X86_64.SH

end

end

/-! ### `MlKem.X86_64.S4Scalar`, which only this module used -/

section

/-!
# ML-KEM on x86-64: `vg_mlkem_sample_ntt4`, verified

The baseline implementation of `vg_mlkem_sample_ntt4` calls
`vg_mlkem_sample_ntt` on each seed, between the prologue and the epilogue of
the one for AVX2; its proofs are the pieces of that one's for the calls
(`S4Parse.lean`, `S4CT.lean`), with nothing to keep of the memory but the
polynomials already sampled.
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64.S4

variable {w16 : Bool}

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlKem.X86_64.Sample4
open VG.Spec.MlKem

/-- Nothing of the memory. -/
abbrev NoX (_ : Mem) : Prop := True

section
variable {σ : State} (hp : PreW w16 σ)
include hp

theorem callK_ok' {K : Nat} (hK : K < 4) {s : State} (h : PCW w16 NoX σ K s) : WP isa (callK K w16) s (PCW w16 NoX σ (K + 1)) :=
  WP.seq (WP.mono (argsK_ok hK h) fun _ h₂ => WP.seq (WP.mono (callK_ok hp hK (fun _ _ _ _ => trivial) h₂)
    fun _ h₃ => andK_ok h₃))

theorem scalar_body_ok {s : State} (h : I0W w16 σ s) :
    WP isa (.seq (callK 0 w16) (.seq (callK 1 w16) (.seq (callK 2 w16) (.seq (callK 3 w16) (.block epi))))) s fun s' =>
      (sample4KW w16).post σ s' ∧ gprPreserved σ s' := by
  have p₀ : PCW w16 NoX σ 0 s := ⟨h.env, trivial, by rw [h.r14]; rfl, fun _ h _ _ => absurd h (by omega_using [])⟩
  exact WP.seq (WP.mono (callK_ok' hp (by decide) p₀) fun _ p₁ => WP.seq (WP.mono (callK_ok' hp (by decide) p₁)
    fun _ p₂ => WP.seq (WP.mono (callK_ok' hp (by decide) p₂) fun _ p₃ =>
      WP.seq (WP.mono (callK_ok' hp (by decide) p₃) fun _ p₄ => end_ok hp p₄))))

end

theorem correct_scalar (σ : State) (hs : (sample4KW w16).pre σ) :
    ∃ t s', Exec isa (Impl.MlKem.X86_64.Sample4.sampleNTT4 w16) σ t s' ∧ abiPreserved σ s' ∧
      (sample4KW w16).post σ s' := by
  have hp := preW_of hs
  obtain ⟨t, s', he, hF⟩ := WP.seq (WP.mono (pro_ok hp) fun _ h => scalar_body_ok hp h)
  exact ⟨t, s', he, abiPreserved_of_exec (by cases w16 <;> decide +kernel) he hF.2, hF.1⟩

/-- The taint analysis of the arguments of the call on seed `K`, of either width. -/
theorem args_taint {K : Nat} (hK : K < 4) (w16 : Bool) : ∃ hc : VG.Taint.Hint X86_64.Taint.T,
    (taint.check (X86_64.Taint.ofRegs [.r12, .r13, .rbx])
      (.block [.mov .rdi (.reg .r12), .alu .add .rdi (.imm (BitVec.ofNat 32 (34 * K))),
        .mov .rsi (.reg .r13), .alu .add .rsi (.imm (BitVec.ofNat 32 (pBytes w16 * K))), .mov .rdx (.reg .rbx),
        .alu .add .rdx (.imm (BitVec.ofNat 32 oScalar))]) hc).isSome = true := by
  rcases (by omega_using [hK] : K = 0 ∨ K = 1 ∨ K = 2 ∨ K = 3) with rfl | rfl | rfl | rfl <;> cases w16 <;>
    exact ⟨_, by taint_decide⟩

/-- The call on seed `K`. -/
theorem callK_ct {K : Nat} (hK : K < 4) :
    RelCT isa (R4W w16 fun σ s => PCW w16 NoX σ K s) (callK K w16) (R4W w16 fun σ s => PCW w16 NoX σ (K + 1) s) := by
  obtain ⟨_, c⟩ := args_taint hK w16
  exact RelCT.seq (args_ct (X := fun _ => NoX) hK c) (RelCT.seq (call_ct hK fun _ _ _ _ _ _ => trivial) and_ct)

theorem ct_scalar : ConstantTime isa (sample4KW w16).pre (sample4KW w16).pub (Impl.MlKem.X86_64.Sample4.sampleNTT4 w16) := by
  refine relStart (Q := fun _ _ => True) (RelCT.seq (RelCT.mono (relInv (I' := fun σ s => PCW w16 NoX σ 0 s)
    (fun σ s hp h => by
      subst h
      exact WP.mono (pro_ok (preW_of hp)) fun _ h => ⟨h.env, trivial, by rw [h.r14]; rfl, fun _ h _ _ => absurd h (by omega_using [])⟩)
    (taintRel [.rdi, .rsi, .rdx] (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
      subst h₁ h₂
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      exacts [hq.1, hq.2.1, hq.2.2.1]) (by taint_decide))) (fun _ _ h => h) fun _ _ h => h) ?_)
  refine RelCT.seq (callK_ct (K := 0) (by decide)) (RelCT.seq (callK_ct (K := 1) (by decide))
    (RelCT.seq (callK_ct (K := 2) (by decide)) (RelCT.seq (callK_ct (K := 3) (by decide)) ?_)))
  exact taintRel [.rbx] (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact env_rbx hq h₁.env h₂.env) (by taint_decide)

end VG.Proof.MlKem.X86_64.S4

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64

theorem sample4_scalar_correct (σ : State) (hs : sample4K.pre σ) :
    ∃ t s', Exec isa Impl.MlKem.X86_64.Sample4.sampleNTT4 σ t s' ∧ abiPreserved σ s' ∧ sample4K.post σ s' := by
  rw [sample4K_eq] at hs ⊢; exact S4.correct_scalar (w16 := false) σ hs

theorem sample4_scalar_ct : ConstantTime isa sample4K.pre sample4K.pub Impl.MlKem.X86_64.Sample4.sampleNTT4 := by
  rw [sample4K_eq]; exact S4.ct_scalar (w16 := false)

end VG.Proof.MlKem.X86_64

end

end

/-!
# Implementations of `vg_mlkem_sample_ntt4` on x86-64

A `Sample4Impl` is what a function that calls `vg_mlkem_sample_ntt4` needs
of it, so that its proof holds for every implementation: each is a variant
of the interface `MlKemSample4` on x86-64 (`Variants/MlKemSample4/X86_64/`),
and each caller (the top-level functions of ML-KEM-768 and ML-KEM-1024, in
`Generic/MlKemSample4/X86_64/`) is emitted once for each of them (see
`TCB/Emit.lean`). Each is proven with 24 bytes of stack below its return
address: the baseline's calls of `vg_mlkem_sample_ntt`, three deep (the
others call nothing).

Those with AVX2 are code with 16-bit coefficients (`Callee4.s16`,
`vg_mlkem16_sample_ntt4_avx2` and `_avx512`), proven against `sample4KW true`
(`S16Ok`), and their callers run with 16-bit polynomials; their functions of
`u32`s, which the callers never run, are the baseline's.

Each also comes with the computation of several outputs of `PRF₂` that its
callers inline (`Callee4.prfs`): one at a time for the baseline, and four
at a time with AVX2 (`Prfs.lean`); and, for
those with AVX2, the fragment encapsulation inlines to sample three entries
of the matrix with 16-bit coefficients while absorbing blocks of `ek`
(`Callee4.batchH16`, `Sample4.sampleH`), with its proofs (`BatchHOk16`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64

/-- What encapsulation needs of a fragment it inlines (`Callee4.batchH16`):
it meets `sampleHKW true`, in constant time, calls nothing, keeps MXCSR's
control bits and never writes the stack pointer. -/
structure BatchHOk16 (b : Prog isa) : Prop where
  ok : ∀ s, (sampleHKW true).pre s → ∃ t s', Exec isa b s t s' ∧ abiPreserved s s' ∧ (sampleHKW true).post s s'
  ct : ConstantTime isa (sampleHKW true).pre (sampleHKW true).pub b
  noCalls : b.noCalls = true
  ctl : ctlOk b = true
  sp : b.all (fun i => !isa.writesSp i) = true
  /-- It uses no stack. -/
  xd : b.x86_64Depth = 0

/-- The checks of every instruction of a fragment, at once. -/
noncomputable def BatchHOk16.checks (b : Prog isa) : Bool :=
  b.noCalls && ctlOk b && b.allInstrs (fun i => !isa.writesSp i) && b.x86_64Depth == 0

/-- `BatchHOk16.checks`, with the tests of an instruction in one match
(`hasBits`, `Proof/Framework/X86_64/InstrBits.lean`) and one walk of the
code for them: what the kernel evaluates, for every fragment of a kind in
one declaration, so that it builds what they share once. -/
noncomputable def BatchHOk16.checksB (b : Prog isa) : Bool :=
  b.noCalls && b.allInstrs (hasBits (bMx + bSp)) && b.x86_64Depth == 0

theorem BatchHOk16.checks_of_B {b : Prog isa} (h : BatchHOk16.checksB b = true) :
    BatchHOk16.checks b = true ∧ b.allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [BatchHOk16.checksB, Bool.and_eq_true] at h
  obtain ⟨⟨hn, hb⟩, hd⟩ := h
  have hm := Code.noMx_of_bits rfl hb
  simp only [BatchHOk16.checks, Bool.and_eq_true]
  exact ⟨⟨⟨⟨hn, ctlOk_of_noLoad hm⟩, Code.sp_of_bits rfl hb⟩, hd⟩, hm⟩

theorem sampleH16_checks (fast : Bool) : BatchHOk16.checks (Impl.MlKem.X86_64.Sample4.sampleH fast true) = true := by
  have h : ([false, true].all fun fast =>
      BatchHOk16.checksB (Impl.MlKem.X86_64.Sample4.sampleH fast true)) = true := by decide +kernel
  exact (BatchHOk16.checks_of_B (List.all_eq_true.mp h fast (by cases fast <;> decide))).1

theorem sampleH16_ok (fast : Bool) : BatchHOk16 (Impl.MlKem.X86_64.Sample4.sampleH fast true) := by
  have h := sampleH16_checks fast
  simp only [BatchHOk16.checks, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨SH.correctW (w16 := true) (fast := fast), SH.ctW (w16 := true) (fast := fast), h.1.1.1, h.1.1.2,
    Code.all_of_allInstrs h.1.2, h.2⟩

/-- What key generation needs of a fragment it inlines absorbing `m` blocks
(`Callee4.batchHM16`): as `BatchHOk16`, with `sampleHMKW true m`. -/
structure BatchHMOk16 (m : Nat) (b : Prog isa) : Prop where
  ok : ∀ s, (sampleHMKW true m).pre s → ∃ t s', Exec isa b s t s' ∧ abiPreserved s s' ∧ (sampleHMKW true m).post s s'
  ct : ConstantTime isa (sampleHMKW true m).pre (sampleHMKW true m).pub b
  noCalls : b.noCalls = true
  ctl : ctlOk b = true
  sp : b.all (fun i => !isa.writesSp i) = true
  /-- It uses no stack. -/
  xd : b.x86_64Depth = 0

theorem sampleHM16_checks (fast : Bool) {m : Nat} (hm : m ≤ 3) :
    BatchHOk16.checks (Impl.MlKem.X86_64.Sample4.sampleHM fast m) = true := by
  have h : ((List.range 4).all fun m => [false, true].all fun fast =>
      BatchHOk16.checksB (Impl.MlKem.X86_64.Sample4.sampleHM fast m)) = true := by decide +kernel
  exact (BatchHOk16.checks_of_B (List.all_eq_true.mp (List.all_eq_true.mp h m
    (List.mem_range.mpr (Nat.lt_succ_of_le hm))) fast (by cases fast <;> decide))).1

theorem sampleHM16_ok (fast : Bool) {m : Nat} (hm : m ≤ 3) : BatchHMOk16 m (Impl.MlKem.X86_64.Sample4.sampleHM fast m) := by
  have h := sampleHM16_checks fast hm
  simp only [BatchHOk16.checks, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨SH.correctHM (fast := fast) hm, SH.ctHM (fast := fast) hm, h.1.1.1, h.1.1.2, Code.all_of_allInstrs h.1.2, h.2⟩

/-- What key generation and encapsulation need of a fragment they inline
computing `m` outputs of `PRF₂` from `PRF₂(σ, N₀)` (`Callee4.batchP16`): as
`BatchHOk16`, with `samplePNKW N₀ m`. -/
structure BatchPOk16 (N₀ m : Nat) (b : Prog isa) : Prop where
  ok : ∀ s, (samplePNKW N₀ m).pre s → ∃ t s', Exec isa b s t s' ∧ abiPreserved s s' ∧ (samplePNKW N₀ m).post s s'
  ct : ConstantTime isa (samplePNKW N₀ m).pre (samplePNKW N₀ m).pub b
  noCalls : b.noCalls = true
  ctl : ctlOk b = true
  sp : b.all (fun i => !isa.writesSp i) = true
  /-- It uses no stack. -/
  xd : b.x86_64Depth = 0

/-- The checks of a fragment computing outputs of `PRF₂`, and that it never
loads MXCSR. -/
noncomputable def BatchPOk16.checks (b : Prog isa) : Bool :=
  BatchHOk16.checks b && b.allInstrs (fun i => !loadsMxcsr i)

theorem samplePN16_checks (fast : Bool) {q : Nat × Nat} (hq : q ∈ Impl.MlKem.X86_64.Sample4.pnUses) :
    BatchPOk16.checks (Impl.MlKem.X86_64.Sample4.samplePN fast q.1 q.2) = true := by
  have h : (Impl.MlKem.X86_64.Sample4.pnUses.all fun q => [false, true].all fun fast =>
      BatchHOk16.checksB (Impl.MlKem.X86_64.Sample4.samplePN fast q.1 q.2)) = true := by decide +kernel
  have hb := BatchHOk16.checks_of_B (List.all_eq_true.mp (List.all_eq_true.mp h q hq) fast (by cases fast <;> decide))
  rw [BatchPOk16.checks, hb.1, hb.2]; rfl

theorem pnUses_le {q : Nat × Nat} (hq : q ∈ Impl.MlKem.X86_64.Sample4.pnUses) : 0 < q.2 ∧ q.2 ≤ 3 ∧ q.1 + q.2 ≤ 256 := by
  simp only [Impl.MlKem.X86_64.Sample4.pnUses, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl <;> decide

theorem samplePN16_ok (fast : Bool) {q : Nat × Nat} (hq : q ∈ Impl.MlKem.X86_64.Sample4.pnUses) :
    BatchPOk16 q.1 q.2 (Impl.MlKem.X86_64.Sample4.samplePN fast q.1 q.2) := by
  have h := samplePN16_checks fast hq
  have hl := pnUses_le hq
  simp only [BatchPOk16.checks, BatchHOk16.checks, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨SH.correctPN (fast := fast) hl.1 hl.2.1 hl.2.2 h.2, SH.ctPN_uses (fast := fast) hq, h.1.1.1.1, h.1.1.1.2,
    Code.all_of_allInstrs h.1.1.2, h.1.2⟩

/-- What a caller needs of an implementation's code with 16-bit
coefficients (`Callee4.s16`): it meets `sample4KW true`, in constant time,
never writes the stack pointer, calls at most three deep and keeps MXCSR's
control bits. -/
structure S16Ok (c : Prog isa) : Prop where
  ok : ∀ s, (sample4KW true).pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (sample4KW true).post s s'
  ct : ConstantTime isa (sample4KW true).pre (sample4KW true).pub c
  nosp : NoSp c
  depth_le : c.depth ≤ 3
  mxcsr : ctlOk c = true
  spSafe : c.all (fun i => !isa.writesSp i) = true

/-- An implementation of `vg_mlkem_sample_ntt4` on x86-64. -/
structure Sample4Impl where
  /-- Its symbol and code. -/
  callee : Impl.MlKem.X86_64.Callee4
  /-- It is correct. -/
  ok : ∀ s, sample4K.pre s → ∃ t s', Exec isa callee.code s t s' ∧ abiPreserved s s' ∧ sample4K.post s s'
  /-- It is constant time. -/
  ct : ConstantTime isa sample4K.pre sample4K.pub callee.code
  /-- It never writes the stack pointer. -/
  nosp : NoSp callee.code
  /-- Its calls are at most three deep. -/
  depth_le : callee.code.depth ≤ 3
  /-- It keeps MXCSR's control bits. -/
  mxcsr : ctlOk callee.code = true
  spSafe : callee.code.all (fun i => !isa.writesSp i) = true
  /-- Its code with 16-bit coefficients, if any, is verified. -/
  s16 : ∀ n c, callee.s16 = some (n, c) → S16Ok c
  /-- Its outputs of `PRF₂` are correct. -/
  prfs_ok : ∀ {rbs wbs : List (Reg × Nat)} {s : State}, Lay rbs wbs s → (∀ b ∈ rbs ++ wbs, b.1 ∈ bases) →
    ∀ {N₀ n o wl : Nat}, N₀ + n + 4 ≤ 256 → prfsChk (rbs ++ wbs) wbs n o wl = true →
      WP isa (callee.prfs N₀ n o wl) s (PrfsPost s N₀ n o wl)
  /-- They are constant time. -/
  prfs_tr : ∀ {rbs wbs : List (Reg × Nat)}, (∀ b ∈ rbs ++ wbs, b.1 ∈ bases) →
    ∀ {N₀ n o wl : Nat}, N₀ + n + 4 ≤ 256 → prfsChk (rbs ++ wbs) wbs n o wl = true →
      RelCT isa (LRel rbs wbs) (callee.prfs N₀ n o wl) fun _ _ => True
  prfs_ctl : ∀ N₀ n o wl, ctlOk (callee.prfs N₀ n o wl) = true
  prfs_sp : ∀ N₀ n o wl, (callee.prfs N₀ n o wl).all (fun i => !isa.writesSp i) = true
  /-- Its calls use at most 16 bytes of stack. -/
  prfs_xd : ∀ N₀ n o wl, (callee.prfs N₀ n o wl).x86_64Depth ≤ 16
  /-- The polynomial arithmetic that goes with it is correct, constant
  time, and safe to call. -/
  arith : ArithOk callee.arith
  /-- Its fragment for encapsulation, if any, is verified. -/
  batchH16 : ∀ b, callee.batchH16 = some b → BatchHOk16 b
  /-- Its fragments for key generation, if any, are verified. -/
  batchHM16 : ∀ b, callee.batchHM16 = some b → ∀ m ≤ 3, BatchHMOk16 m (b m)
  /-- Its fragments computing outputs of `PRF₂` for key generation and
  encapsulation, if any, are verified, for each of their uses. -/
  batchP16 : ∀ b, callee.batchP16 = some b → ∀ q ∈ Impl.MlKem.X86_64.Sample4.pnUses, BatchPOk16 q.1 q.2 (b q.1 q.2)
  /-- What the names of its callers' instances end with (e.g. `_avx2`;
  nothing for the baseline implementation). -/
  suffix : String
  /-- How its callers compute the outputs of `PRF₂`, for their documentation. -/
  prfsDoc : String
  /-- The CPU features its code requires, which its callers require too. -/
  features : List String

namespace Sample4Impl

/-- The checks of every instruction of an implementation's code, at once:
the kernel builds the code once for all four. -/
noncomputable def codeChecks (c : Prog isa) : Bool :=
  c.allInstrs (fun i => !Taint.clobbers i .rsp) && decide (c.depth ≤ 3) && ctlOk c &&
    c.allInstrs (fun i => !isa.writesSp i)

theorem codeChecks_spec {c : Prog isa} (h : codeChecks c = true) :
    NoSp c ∧ c.depth ≤ 3 ∧ ctlOk c = true ∧ c.all (fun i => !isa.writesSp i) = true := by
  simp only [codeChecks, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨nosp_of h.1.1.1, h.1.1.2, h.1.2, Code.all_of_allInstrs h.2⟩

/-- `codeChecks`, with the tests of an instruction in one match (`hasBits`)
and one walk of the code for them: what the kernel evaluates. -/
noncomputable def codeChecksB (c : Prog isa) : Bool :=
  c.allInstrs (hasBits (bMx + bSp + bNs)) && decide (c.depth ≤ 3)

theorem codeChecks_of_B {c : Prog isa} (h : codeChecksB c = true) : codeChecks c = true := by
  simp only [codeChecksB, Bool.and_eq_true] at h
  simp only [codeChecks, Bool.and_eq_true]
  exact ⟨⟨⟨Code.noRsp_of_bits rfl h.1, h.2⟩, ctlOk_of_noLoad (Code.noMx_of_bits rfl h.1)⟩, Code.sp_of_bits rfl h.1⟩

theorem scalar_checks : codeChecks (Impl.MlKem.X86_64.Callee4.scalar).code = true :=
  codeChecks_of_B (by decide +kernel)

/-- The baseline implementation, `vg_mlkem_sample_ntt4`, which calls `vg_mlkem_sample_ntt`. -/
def scalar : Sample4Impl where
  callee := .scalar
  ok := sample4_scalar_correct
  ct := sample4_scalar_ct
  nosp := (codeChecks_spec scalar_checks).1
  depth_le := (codeChecks_spec scalar_checks).2.1
  mxcsr := (codeChecks_spec scalar_checks).2.2.1
  spSafe := (codeChecks_spec scalar_checks).2.2.2
  s16 := fun _ _ h => nomatch h
  prfs_ok := fun L hcs => prfsScalar_ok L hcs
  prfs_tr := fun hcs => prfsScalar_tr hcs
  prfs_ctl := prfsScalar_ctl
  prfs_sp := prfsScalar_sp
  prfs_xd := prfsScalar_xd
  arith := ArithOk.sse
  batchH16 := fun _ h => nomatch h
  batchHM16 := fun _ h => nomatch h
  batchP16 := fun _ h => nomatch h
  suffix := ""
  prfsDoc := "one at a time"
  features := []

/-- The checks of the AVX2 and the AVX-512 code, which share most of it, at once. -/
theorem avx_checks16 (fast : Bool) : codeChecks (Impl.MlKem.X86_64.Sample4.sampleNTT4Avx2 fast true) = true := by
  have h : ([false, true].all fun fast =>
      codeChecksB (Impl.MlKem.X86_64.Sample4.sampleNTT4Avx2 fast true)) = true := by decide +kernel
  exact codeChecks_of_B (List.all_eq_true.mp h fast (by cases fast <;> decide))

theorem avx2_checks16 : codeChecks (Impl.MlKem.X86_64.Sample4.sampleNTT4Avx2 false true) = true := avx_checks16 false

theorem avx2_s16 : S16Ok (Impl.MlKem.X86_64.Sample4.sampleNTT4Avx2 false true) :=
  ⟨S4.correct (w16 := true) (fast := false), S4.ct (w16 := true) (fast := false), (codeChecks_spec avx2_checks16).1,
    (codeChecks_spec avx2_checks16).2.1, (codeChecks_spec avx2_checks16).2.2.1, (codeChecks_spec avx2_checks16).2.2.2⟩

/-- The AVX2 implementation, `vg_mlkem16_sample_ntt4_avx2`: its callers run with 16-bit
polynomials, and its functions of `u32`s, which they never run, are the baseline's. -/
def avx2 : Sample4Impl where
  callee := .avx2
  ok := sample4_scalar_correct
  ct := sample4_scalar_ct
  nosp := (codeChecks_spec scalar_checks).1
  depth_le := (codeChecks_spec scalar_checks).2.1
  mxcsr := (codeChecks_spec scalar_checks).2.2.1
  spSafe := (codeChecks_spec scalar_checks).2.2.2
  s16 := fun _ _ h => by injection h with h; cases h; exact avx2_s16
  prfs_ok := fun L hcs => prfsAvx2_ok L hcs
  prfs_tr := fun hcs => prfsAvx2_tr hcs
  prfs_ctl := prfsAvx2_ctl
  prfs_sp := prfsAvx2_sp
  prfs_xd := prfsAvx2_xd
  arith := ArithOk.sse16
  batchH16 := fun _ h => Option.some.inj h ▸ sampleH16_ok false
  batchHM16 := fun _ h m hm => Option.some.inj h ▸ sampleHM16_ok false hm
  batchP16 := fun _ h _ hq => Option.some.inj h ▸ samplePN16_ok false hq
  suffix := "_avx2"
  prfsDoc := "four at a time, with AVX2 (and the first one or two of `4k + 1` or `4k + 2` on their own)"
  features := ["avx", "avx2"]

theorem avx512_checks16 : codeChecks (Impl.MlKem.X86_64.Sample4.sampleNTT4Avx2 true true) = true := avx_checks16 true

theorem avx512_s16 : S16Ok (Impl.MlKem.X86_64.Sample4.sampleNTT4Avx2 true true) :=
  ⟨S4.correct (w16 := true) (fast := true), S4.ct (w16 := true) (fast := true), (codeChecks_spec avx512_checks16).1,
    (codeChecks_spec avx512_checks16).2.1, (codeChecks_spec avx512_checks16).2.2.1, (codeChecks_spec avx512_checks16).2.2.2⟩

/-- The AVX-512 implementation, `vg_mlkem16_sample_ntt4_avx512`: as `avx2`, with
AVX-512VL quadword rotates, and sixteen iterations of `SampleNTT`'s loop at a
time with AVX512BW (`Sample4.zgrp`). -/
def avx512 : Sample4Impl where
  callee := .avx512
  ok := sample4_scalar_correct
  ct := sample4_scalar_ct
  nosp := (codeChecks_spec scalar_checks).1
  depth_le := (codeChecks_spec scalar_checks).2.1
  mxcsr := (codeChecks_spec scalar_checks).2.2.1
  spSafe := (codeChecks_spec scalar_checks).2.2.2
  s16 := fun _ _ h => by injection h with h; cases h; exact avx512_s16
  prfs_ok := fun L hcs => prfsAvx2_ok L hcs
  prfs_tr := fun hcs => prfsAvx2_tr hcs
  prfs_ctl := prfsAvx2_ctl
  prfs_sp := prfsAvx2_sp
  prfs_xd := prfsAvx2_xd
  arith := ArithOk.sse16
  batchH16 := fun _ h => Option.some.inj h ▸ sampleH16_ok true
  batchHM16 := fun _ h m hm => Option.some.inj h ▸ sampleHM16_ok true hm
  batchP16 := fun _ h _ hq => Option.some.inj h ▸ samplePN16_ok true hq
  suffix := "_avx512"
  prfsDoc := "four at a time, with AVX-512VL quadword rotates (and the first one or two of `4k + 1` or `4k + 2` on their own)"
  features := ["avx", "avx2", "avx512f", "avx512vl", "avx512bw"]

end Sample4Impl

open Lean Elab Tactic in
/-- Fails if the goal mentions the variable `v`: the kernel evaluates only
code that does not call the implementation `v`, each part once (rather than
failing on code that does, after evaluating its other parts). -/
elab "closed_in " v:ident : tactic => withMainContext do
  let e ← elabTerm v none
  if (← instantiateMVars (← getMainTarget)).containsFVar e.fvarId! then
    throwError "the goal mentions {e}"

/-- `ctlOk` of code that calls the implementation `v`: evaluated by the
kernel but for the calls of `v`. -/
tactic_template "s4_ctl " v:ident : tactic =>
  `(tactic| repeat' (first
    | (closed_in $v; decide +kernel) | with_reducible exact ($v).arith.dm_ctl
    | with_reducible exact ($v).arith.em_ctl | with_reducible exact ($v).arith.km_ctl | apply ctlOk_seq | apply ctlOk_ite
    | (apply ctlOk_call; exact ($v).mxcsr) | exact ($v).prfs_ctl _ _ _ _
    | exact ($v).arith.nttInv.ctl | exact ($v).arith.add.ctl | exact ($v).arith.sub.ctl
    | exact ($v).arith.cbd.ctl | exact ($v).arith.cbd16.ctl | exact ($v).arith.dec12.ctl | exact ($v).arith.enc12.ctl | exact Codecs.ce_ctl _ | exact Codecs.dd_ctl _
    | rfl))

/-- Code that does not call the implementation `v` never writes the stack pointer: by evaluation. -/
tactic_template "s4_sp_closed " v:ident : tactic =>
  `(tactic| (closed_in $v; exact Code.all_of_spTest (by decide +kernel)))

/-- That code that calls the implementation `v` never writes the stack pointer. -/
tactic_template "s4_sp " v:ident : tactic =>
  `(tactic| repeat' (first
    | s4_sp_closed $v | with_reducible exact ($v).arith.dm_sp | with_reducible exact ($v).arith.em_sp | with_reducible exact ($v).arith.km_sp
    | apply all_seq | apply all_ite
    | (apply all_call; exact ($v).spSafe) | exact ($v).prfs_sp _ _ _ _
    | exact ($v).arith.nttInv.sp | exact ($v).arith.add.sp | exact ($v).arith.sub.sp
    | exact ($v).arith.cbd.sp | exact ($v).arith.cbd16.sp | exact ($v).arith.dec12.sp | exact ($v).arith.enc12.sp | exact Codecs.ce_sp _ | exact Codecs.dd_sp _
    | rfl))

end VG.Proof.MlKem.X86_64
