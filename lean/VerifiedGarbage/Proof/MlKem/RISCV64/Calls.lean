module

public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.MlKem.RISCV64.HashTop
public import VerifiedGarbage.Proof.MlKem.RISCV64.Prims
public import VerifiedGarbage.Proof.MlKem.RISCV64.Ntt
public import VerifiedGarbage.Proof.MlKem.RISCV64.Cbd2
public import VerifiedGarbage.Proof.MlKem.RISCV64.Decode12
public import VerifiedGarbage.Proof.MlKem.RISCV64.Encode12
public import VerifiedGarbage.Proof.MlKem.RISCV64.CompressEncode
public import VerifiedGarbage.Proof.MlKem.RISCV64.DecodeDecompress
public import VerifiedGarbage.Proof.MlKem.RISCV64.Sample
import VerifiedGarbage.Proof.MlKem.RISCV64.NttInv
import VerifiedGarbage.Proof.MlKem.RISCV64.SampleCT
import VerifiedGarbage.Proof.MlKem.Arith
import VerifiedGarbage.Proof.MlKem.Encode
import VerifiedGarbage.Proof.Sha3.RISCV64.Stream.Lit
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.RISCV64.Lit
import VerifiedGarbage.Proof.Framework.Covers
meta import VerifiedGarbage.Proof.Sha3.RISCV64.Stream.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.RISCV64.Lit
public import VerifiedGarbage.Impl.MlKem.RISCV64.Top
public import VerifiedGarbage.Proof.Framework.RISCV64.CallAny
public import VerifiedGarbage.Proof.MlKem.RISCV64.Lay

/-!
# ML-KEM on RISC-V: calling the primitives on buffers

As on PPC64LE (`Proof/MlKem/PPC64LE/Calls.lean`), with the alignment the RISC-V
contracts need of the polynomials and the working space (`Lay.Al`). For each primitive, a
contract written with the precondition of its proof and what its correctness
proof shows (`kNtt`, …, as `kAdd` in `Prims.lean`), and the call of it with
its arguments at offsets in the buffers of a layout (`addL`, …): what it needs
(the arguments in the registers, the regions apart and permitted), what it
changes (`Kept`, with the regions as triples) and what it computes.
-/

@[expose] public section

namespace VG.Proof.MlKem.RISCV64

open VG VG.RISCV64 VG.Impl.MlKem.RISCV64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-- The address at offset `o` of buffer `i`. -/
abbrev Lay.A (L : Lay) (i o : Nat) : Addr := L.ptr i + BitVec.ofNat 64 o

/-- A whole buffer, as a permitted region. -/
abbrev Lay.buf (L : Lay) (i : Nat) : Region := ⟨L.ptr i, L.size i⟩

/-- The address at offset `o` of buffer `i` is 8-byte aligned. -/
def Lay.Al (L : Lay) (i o : Nat) : Prop := (L.A i o).toNat % 8 = 0

theorem Lay.Al.four {L : Lay} {i o : Nat} (h : L.Al i o) : (L.A i o).toNat % 4 = 0 := by
  unfold Lay.Al at h; omega

theorem Lay.fitB {L : Lay} (hL : L.Ok) {i o l : Nat} (hb : i < L.sizes.length ∧ o + l ≤ L.sizes.getD i 0)
    (hl : 0 < l) : (L.A i o).toNat + l ≤ 2 ^ 64 :=
  Lay.fit_off hL hb.1 hb.2 hl

theorem view_r3 (s : State) (rd wr : List Region) : (view s rd wr).gpr .a0 = s.gpr .a0 := view_gpr' _ _ _ (by decide)
theorem view_r4 (s : State) (rd wr : List Region) : (view s rd wr).gpr .a1 = s.gpr .a1 := view_gpr' _ _ _ (by decide)
theorem view_r5 (s : State) (rd wr : List Region) : (view s rd wr).gpr .a2 = s.gpr .a2 := view_gpr' _ _ _ (by decide)
theorem view_r6 (s : State) (rd wr : List Region) : (view s rd wr).gpr .a3 = s.gpr .a3 := view_gpr' _ _ _ (by decide)

theorem mem_rd_wr {r : Region} {s : State} (h : r ∈ s.wr) : r ∈ s.rd ++ s.wr := List.mem_append_right _ h

/-! ## `vg_mlkem_add`, `vg_mlkem_sub` -/

theorem accL {L : Lay} {s : State} (hL : L.Ok) {i o j o' : Nat}
    (g3 : s.gpr .a0 = L.A i o) (g4 : s.gpr .a1 = L.A j o')
    (hs : sepB L.sizes (i, o, 1024) (j, o', 1024) = true) (hw : L.buf i ∈ s.wr) (hr : L.buf j ∈ s.rd ++ s.wr)
    {f g : Poly} (hf : PolyIs s.mem (L.A i o) f) (hg : PolyIs s.mem (L.A j o') g) (ai : L.Al i o)
    (aj : L.Al j o') :
    AccArgs s (L.A i o) (L.A j o') :=
  ⟨g3, g4, Lay.disj hL hs, Lay.fitB hL (sepB_bounds hs) (by decide),
    Lay.fitB hL (sepB_bounds (sepB_symm hs)) (by decide), hf.1, hg.1, ai.four, aj.four,
    Lay.covers hw (sepB_bounds hs).2, Lay.covers hr (sepB_bounds (sepB_symm hs)).2⟩

theorem addL {L : Lay} {s : State} (hL : L.Ok) {i o j o' : Nat}
    (g3 : s.gpr .a0 = L.A i o) (g4 : s.gpr .a1 = L.A j o')
    (hs : sepB L.sizes (i, o, 1024) (j, o', 1024) = true) (hw : L.buf i ∈ s.wr) (hr : L.buf j ∈ s.rd ++ s.wr)
    {f g : Poly} (hf : PolyIs s.mem (L.A i o) f) (hg : PolyIs s.mem (L.A j o') g) (ai : L.Al i o)
    (aj : L.Al j o') {Q : State → Prop}
    (hQ : ∀ s', Kept (L.RL [(i, o, 1024)]) s s' → PolyIs s'.mem (L.A i o) (add f g) → Q s') :
    WP isa callAdd s Q :=
  add_call (accL hL g3 g4 hs hw hr hf hg ai aj) fun s' hk hp => hQ s' hk (by rw [hf.2, hg.2] at hp; exact hp)

theorem subL {L : Lay} {s : State} (hL : L.Ok) {i o j o' : Nat}
    (g3 : s.gpr .a0 = L.A i o) (g4 : s.gpr .a1 = L.A j o')
    (hs : sepB L.sizes (i, o, 1024) (j, o', 1024) = true) (hw : L.buf i ∈ s.wr) (hr : L.buf j ∈ s.rd ++ s.wr)
    {f g : Poly} (hf : PolyIs s.mem (L.A i o) f) (hg : PolyIs s.mem (L.A j o') g) (ai : L.Al i o)
    (aj : L.Al j o') {Q : State → Prop}
    (hQ : ∀ s', Kept (L.RL [(i, o, 1024)]) s s' → PolyIs s'.mem (L.A i o) (sub f g) → Q s') :
    WP isa callSub s Q :=
  sub_call (accL hL g3 g4 hs hw hr hf hg ai aj) fun s' hk hp => hQ s' hk (by rw [hf.2, hg.2] at hp; exact hp)

/-! ## `vg_mlkem_multiply_ntts` -/

theorem mulArgsL {L : Lay} {s : State} (hL : L.Ok) {ih oh jf of kg og ls os : Nat}
    (g3 : s.gpr .a0 = L.A ih oh) (g4 : s.gpr .a1 = L.A jf of)
    (g5 : s.gpr .a2 = L.A kg og) (g6 : s.gpr .a3 = L.A ls os)
    (s_hf : sepB L.sizes (ih, oh, 1024) (jf, of, 1024) = true) (s_hg : sepB L.sizes (ih, oh, 1024) (kg, og, 1024) = true)
    (s_hs : sepB L.sizes (ih, oh, 1024) (ls, os, 1024) = true) (s_fs : sepB L.sizes (jf, of, 1024) (ls, os, 1024) = true)
    (s_gs : sepB L.sizes (kg, og, 1024) (ls, os, 1024) = true)
    (wh : L.buf ih ∈ s.wr) (wf : L.buf jf ∈ s.rd ++ s.wr) (wg : L.buf kg ∈ s.rd ++ s.wr) (ws : L.buf ls ∈ s.wr)
    {f g : Poly} (hf : PolyIs s.mem (L.A jf of) f) (hg : PolyIs s.mem (L.A kg og) g)
    (ah : L.Al ih oh) (af : L.Al jf of) (ag : L.Al kg og) (as : L.Al ls os) :
    MulArgs s (L.A ih oh) (L.A jf of) (L.A kg og) (L.A ls os) :=
  ⟨g3, g4, g5, g6, Lay.disj hL s_hf, Lay.disj hL s_hg, Lay.disj hL s_hs, Lay.disj hL s_fs, Lay.disj hL s_gs,
    Lay.fitB hL (sepB_bounds s_hf) (by decide), Lay.fitB hL (sepB_bounds s_fs) (by decide),
    Lay.fitB hL (sepB_bounds s_gs) (by decide), Lay.fitB hL (sepB_bounds (sepB_symm s_hs)) (by decide), hf.1, hg.1,
    ah.four, af.four, ag.four, as,
    covers_cons' (Lay.covers wh (sepB_bounds s_hf).2)
      (covers_cons' (Lay.covers ws (sepB_bounds (sepB_symm s_hs)).2) covers_nil'),
    covers_cons' (Lay.covers wf (sepB_bounds s_fs).2) (covers_cons' (Lay.covers wg (sepB_bounds s_gs).2) covers_nil')⟩

theorem mulL {L : Lay} {s : State} (hL : L.Ok) {ih oh jf of kg og ls os : Nat}
    (g3 : s.gpr .a0 = L.A ih oh) (g4 : s.gpr .a1 = L.A jf of)
    (g5 : s.gpr .a2 = L.A kg og) (g6 : s.gpr .a3 = L.A ls os)
    (s_hf : sepB L.sizes (ih, oh, 1024) (jf, of, 1024) = true) (s_hg : sepB L.sizes (ih, oh, 1024) (kg, og, 1024) = true)
    (s_hs : sepB L.sizes (ih, oh, 1024) (ls, os, 1024) = true) (s_fs : sepB L.sizes (jf, of, 1024) (ls, os, 1024) = true)
    (s_gs : sepB L.sizes (kg, og, 1024) (ls, os, 1024) = true)
    (wh : L.buf ih ∈ s.wr) (wf : L.buf jf ∈ s.rd ++ s.wr) (wg : L.buf kg ∈ s.rd ++ s.wr) (ws : L.buf ls ∈ s.wr)
    {f g : Poly} (hf : PolyIs s.mem (L.A jf of) f) (hg : PolyIs s.mem (L.A kg og) g)
    (ah : L.Al ih oh) (af : L.Al jf of) (ag : L.Al kg og) (as : L.Al ls os) {Q : State → Prop}
    (hQ : ∀ s', Kept (L.RL [(ih, oh, 1024), (ls, os, 1024)]) s s' → PolyIs s'.mem (L.A ih oh) (multiplyNTTs f g) →
      Q s') :
    WP isa callMul s Q :=
  mul_call (mulArgsL hL g3 g4 g5 g6 s_hf s_hg s_hs s_fs s_gs wh wf wg ws hf hg ah af ag as) fun s' hk hp =>
    hQ s' hk (by rw [hf.2, hg.2] at hp; exact hp)

/-! ## `vg_mlkem_ntt`, `vg_mlkem_inv_ntt` -/

def kNtt : Contract isa := mkK Ntt.Pre (fun s₀ s => PolyIs s.mem (Ntt.F s₀) (ntt (Ntt.P s₀))) (regsEq [.a0, .a1])

def kNttInv : Contract isa :=
  mkK Ntt.Pre (fun s₀ s => PolyIs s.mem (Ntt.F s₀) (nttInv (Ntt.P s₀))) (regsEq [.a0, .a1])

theorem kNtt_ok : ∀ s, kNtt.pre s → ∃ t s', Exec isa Impl.MlKem.RISCV64.ntt s t s' ∧ abiPreserved s s' ∧
    kNtt.post s s' := mkK_ok fun _ hp => Ntt.correct hp

theorem kNttInv_ok : ∀ s, kNttInv.pre s → ∃ t s', Exec isa Impl.MlKem.RISCV64.nttInv s t s' ∧ abiPreserved s s' ∧
    kNttInv.post s s' := mkK_ok fun _ hp => NttInv.correct hp

theorem ntt_pre {L : Lay} {s : State} (hL : L.Ok) {i o j o' : Nat}
    (g3 : s.gpr .a0 = L.A i o) (g4 : s.gpr .a1 = L.A j o')
    (hs : sepB L.sizes (i, o, 1024) (j, o', 1024) = true) (wi : L.buf i ∈ s.wr) (wj : L.buf j ∈ s.wr)
    {f : Poly} (hf : PolyIs s.mem (L.A i o) f) (ai : L.Al i o) (aj : L.Al j o') :
    Ntt.Pre (view s [] [polyRegion (L.A i o), polyRegion (L.A j o')]) ∧
      Covers ([] ++ [polyRegion (L.A i o), polyRegion (L.A j o')]) (s.rd ++ s.wr) ∧
      Covers [polyRegion (L.A i o), polyRegion (L.A j o')] s.wr ∧
      Ntt.F (view s [] [polyRegion (L.A i o), polyRegion (L.A j o')]) = L.A i o ∧
      Ntt.P (view s [] [polyRegion (L.A i o), polyRegion (L.A j o')]) = f := by
  have cw : Covers [polyRegion (L.A i o), polyRegion (L.A j o')] s.wr :=
    covers_cons' (Lay.covers wi (sepB_bounds hs).2) (covers_cons' (Lay.covers wj (sepB_bounds (sepB_symm hs)).2)
      covers_nil')
  have eF : Ntt.F (view s [] [polyRegion (L.A i o), polyRegion (L.A j o')]) = L.A i o := by
    simp only [Ntt.F, view_r3, g3]
  have eS : Ntt.S (view s [] [polyRegion (L.A i o), polyRegion (L.A j o')]) = L.A j o' := by
    simp only [Ntt.S, view_r4, g4]
  refine ⟨⟨rfl, by rw [eF, eS]; rfl, by rw [eF, eS]; exact Lay.disj hL hs,
    by rw [eF]; exact Lay.fitB hL (sepB_bounds hs) (by decide),
    by rw [eS]; exact Lay.fitB hL (sepB_bounds (sepB_symm hs)) (by decide), by rw [eF]; exact hf.1,
    by rw [eF]; exact ai.four, by rw [eS]; exact aj⟩,
    covers_wr cw, cw, eF, ?_⟩
  simp only [Ntt.P, eF, State.withRegions_mem, State.callEntry_mem, hf.2]

theorem nttL {L : Lay} {s : State} (hL : L.Ok) {i o j o' : Nat}
    (g3 : s.gpr .a0 = L.A i o) (g4 : s.gpr .a1 = L.A j o')
    (hs : sepB L.sizes (i, o, 1024) (j, o', 1024) = true) (wi : L.buf i ∈ s.wr) (wj : L.buf j ∈ s.wr)
    {f : Poly} (hf : PolyIs s.mem (L.A i o) f) (ai : L.Al i o) (aj : L.Al j o') {Q : State → Prop}
    (hQ : ∀ s', Kept (L.RL [(i, o, 1024), (j, o', 1024)]) s s' → PolyIs s'.mem (L.A i o) (ntt f) → Q s') :
    WP isa callNtt s Q := by
  obtain ⟨hp, c1, c2, eF, eP⟩ := ntt_pre hL g3 g4 hs wi wj hf ai aj
  refine call_kept (k := kNtt) kNtt_ok (by decide +kernel) hp c1 c2 fun s' hk hq => hQ s' hk ?_
  simp only [kNtt, mkK, eF, eP, State.withRegions_mem] at hq; exact hq

theorem nttInvL {L : Lay} {s : State} (hL : L.Ok) {i o j o' : Nat}
    (g3 : s.gpr .a0 = L.A i o) (g4 : s.gpr .a1 = L.A j o')
    (hs : sepB L.sizes (i, o, 1024) (j, o', 1024) = true) (wi : L.buf i ∈ s.wr) (wj : L.buf j ∈ s.wr)
    {f : Poly} (hf : PolyIs s.mem (L.A i o) f) (ai : L.Al i o) (aj : L.Al j o') {Q : State → Prop}
    (hQ : ∀ s', Kept (L.RL [(i, o, 1024), (j, o', 1024)]) s s' → PolyIs s'.mem (L.A i o) (nttInv f) → Q s') :
    WP isa callNttInv s Q := by
  obtain ⟨hp, c1, c2, eF, eP⟩ := ntt_pre hL g3 g4 hs wi wj hf ai aj
  refine call_kept (k := kNttInv) kNttInv_ok (by decide +kernel) hp c1 c2 fun s' hk hq => hQ s' hk ?_
  simp only [kNttInv, mkK, eF, eP, State.withRegions_mem] at hq; exact hq

/-! ## `vg_mlkem_cbd2`, `vg_mlkem_decode12`, `vg_mlkem_encode12` -/

def kCbd : Contract isa := mkK Cbd2.Pre (fun s₀ s => PolyIs s.mem (Cbd2.F s₀) (Cbd2.D s₀)) (regsEq [.a0, .a1])

theorem kCbd_ok : ∀ s, kCbd.pre s → ∃ t s', Exec isa Impl.MlKem.RISCV64.cbd2 s t s' ∧ abiPreserved s s' ∧
    kCbd.post s s' :=
  mkK_ok fun s₀ hp => WP.mono (Cbd2.loop_ok hp) fun _ h => ⟨h.pres, h.sp, h.ra,
    polyIs_of_coeffAt (p := Cbd2.F s₀) fun j hj => by
      rw [h.coeff j (by rw [VG.Proof.MlKem.n_eq] at hj; exact hj),
        ite_eq_left (by rw [VG.Proof.MlKem.n_eq] at hj; omega)]; rfl⟩

def kDec : Contract isa := mkK Decode12.Pre (fun s₀ s => PolyIs s.mem (Decode12.F s₀) (Decode12.D s₀))
  (regsEq [.a0, .a1])

theorem kDec_ok : ∀ s, kDec.pre s → ∃ t s', Exec isa Impl.MlKem.RISCV64.decode12 s t s' ∧ abiPreserved s s' ∧
    kDec.post s s' :=
  mkK_ok fun s₀ hp => WP.mono (Decode12.loop_ok hp) fun _ h => ⟨h.pres, h.sp, h.ra,
    polyIs_of_coeffAt (p := Decode12.F s₀) fun j hj => by
      rw [h.coeff j (by rw [VG.Proof.MlKem.n_eq] at hj; exact hj),
        ite_eq_left (by rw [VG.Proof.MlKem.n_eq] at hj; omega)]; rfl⟩

def kEnc : Contract isa := mkK Encode12.Pre (fun s₀ s => bytesAt s.mem (Encode12.O s₀) 384 = Encode12.E s₀)
  (regsEq [.a0, .a1])

theorem kEnc_ok : ∀ s, kEnc.pre s → ∃ t s', Exec isa Impl.MlKem.RISCV64.encode12 s t s' ∧ abiPreserved s s' ∧
    kEnc.post s s' :=
  mkK_ok fun s₀ hp => WP.mono (Encode12.loop_ok hp) fun _ h => ⟨h.pres, h.sp, h.ra,
    bytesAt_eq! (p := Encode12.O s₀) (encode12_length _) fun k hk => by
      rw [h.bytes k hk, ite_eq_left (by omega)]⟩

/-- `SamplePolyCBD₂` of the 128 bytes at `(i, o)` into the polynomial at `(j, o')`. -/
theorem cbd2L {L : Lay} {s : State} (hL : L.Ok) {i o j o' : Nat}
    (g3 : s.gpr .a0 = L.A i o) (g4 : s.gpr .a1 = L.A j o')
    (hs : sepB L.sizes (i, o, 128) (j, o', 1024) = true) (wi : L.buf i ∈ s.rd ++ s.wr) (wj : L.buf j ∈ s.wr)
    (aj : L.Al j o') {Q : State → Prop}
    (hQ : ∀ s', Kept (L.RL [(j, o', 1024)]) s s' →
      PolyIs s'.mem (L.A j o') (samplePolyCBD 2 (bytesAt s.mem (L.A i o) 128)) → Q s') :
    WP isa callCbd2 s Q := by
  have eB : Cbd2.B (view s [⟨L.A i o, 128⟩] [polyRegion (L.A j o')]) = L.A i o := by
    simp only [Cbd2.B, view_r3, g3]
  have eF : Cbd2.F (view s [⟨L.A i o, 128⟩] [polyRegion (L.A j o')]) = L.A j o' := by
    simp only [Cbd2.F, view_r4, g4]
  have cw : Covers [polyRegion (L.A j o')] s.wr := Lay.covers wj (sepB_bounds (sepB_symm hs)).2
  refine call_kept (k := kCbd) kCbd_ok (by decide +kernel) (rd := [⟨L.A i o, 128⟩]) (wr := [polyRegion (L.A j o')])
    ⟨by simp only [Cbd2.inR, eB, State.withRegions_rd], by simp only [eF, State.withRegions_wr],
      by simp only [Cbd2.inR, eB, eF]; exact Lay.disj hL hs,
      by rw [eB]; exact Lay.fitB hL (sepB_bounds hs) (by decide),
      by rw [eF]; exact Lay.fitB hL (sepB_bounds (sepB_symm hs)) (by decide), by rw [eF]; exact aj.four⟩
    (covers_append (Lay.covers wi (sepB_bounds hs).2) (covers_wr cw)) cw fun s' hk hq => hQ s' hk ?_
  simp only [kCbd, mkK, Cbd2.D, eB, eF, State.withRegions_mem, State.callEntry_mem] at hq; exact hq

/-- `ByteDecode₁₂` of the 384 bytes at `(i, o)` into the polynomial at `(j, o')`. -/
theorem decode12L {L : Lay} {s : State} (hL : L.Ok) {i o j o' : Nat}
    (g3 : s.gpr .a0 = L.A i o) (g4 : s.gpr .a1 = L.A j o')
    (hs : sepB L.sizes (i, o, 384) (j, o', 1024) = true) (wi : L.buf i ∈ s.rd ++ s.wr) (wj : L.buf j ∈ s.wr)
    (aj : L.Al j o') {Q : State → Prop}
    (hQ : ∀ s', Kept (L.RL [(j, o', 1024)]) s s' →
      PolyIs s'.mem (L.A j o') (decode12 (bytesAt s.mem (L.A i o) 384)) → Q s') :
    WP isa callDecode12 s Q := by
  have eB : Decode12.B (view s [⟨L.A i o, 384⟩] [polyRegion (L.A j o')]) = L.A i o := by
    simp only [Decode12.B, view_r3, g3]
  have eF : Decode12.F (view s [⟨L.A i o, 384⟩] [polyRegion (L.A j o')]) = L.A j o' := by
    simp only [Decode12.F, view_r4, g4]
  have cw : Covers [polyRegion (L.A j o')] s.wr := Lay.covers wj (sepB_bounds (sepB_symm hs)).2
  refine call_kept (k := kDec) kDec_ok (by decide +kernel) (rd := [⟨L.A i o, 384⟩]) (wr := [polyRegion (L.A j o')])
    ⟨by simp only [Decode12.inR, eB, State.withRegions_rd], by simp only [eF, State.withRegions_wr],
      by simp only [Decode12.inR, eB, eF]; exact Lay.disj hL hs,
      by rw [eB]; exact Lay.fitB hL (sepB_bounds hs) (by decide),
      by rw [eF]; exact Lay.fitB hL (sepB_bounds (sepB_symm hs)) (by decide), by rw [eF]; exact aj.four⟩
    (covers_append (Lay.covers wi (sepB_bounds hs).2) (covers_wr cw)) cw fun s' hk hq => hQ s' hk ?_
  simp only [kDec, mkK, Decode12.D, eB, eF, State.withRegions_mem, State.callEntry_mem] at hq; exact hq

/-- `ByteEncode₁₂` of the polynomial at `(i, o)` into the 384 bytes at `(j, o')`. -/
theorem encode12L {L : Lay} {s : State} (hL : L.Ok) {i o j o' : Nat}
    (g3 : s.gpr .a0 = L.A i o) (g4 : s.gpr .a1 = L.A j o')
    (hs : sepB L.sizes (i, o, 1024) (j, o', 384) = true) (wi : L.buf i ∈ s.rd ++ s.wr) (wj : L.buf j ∈ s.wr)
    {f : Poly} (hf : PolyIs s.mem (L.A i o) f) (ai : L.Al i o) {Q : State → Prop}
    (hQ : ∀ s', Kept (L.RL [(j, o', 384)]) s s' → bytesAt s'.mem (L.A j o') 384 = encode12 f → Q s') :
    WP isa callEncode12 s Q := by
  have eF : Encode12.F (view s [polyRegion (L.A i o)] [⟨L.A j o', 384⟩]) = L.A i o := by
    simp only [Encode12.F, view_r3, g3]
  have eO : Encode12.O (view s [polyRegion (L.A i o)] [⟨L.A j o', 384⟩]) = L.A j o' := by
    simp only [Encode12.O, view_r4, g4]
  have cw : Covers [⟨L.A j o', 384⟩] s.wr := Lay.covers wj (sepB_bounds (sepB_symm hs)).2
  refine call_kept (k := kEnc) kEnc_ok (by decide +kernel) (rd := [polyRegion (L.A i o)]) (wr := [⟨L.A j o', 384⟩])
    ⟨by simp only [eF, State.withRegions_rd], by simp only [Encode12.outR, eO, State.withRegions_wr],
      by simp only [Encode12.outR, eF, eO]; exact Lay.disj hL hs,
      by rw [eF]; exact Lay.fitB hL (sepB_bounds hs) (by decide),
      by rw [eO]; exact Lay.fitB hL (sepB_bounds (sepB_symm hs)) (by decide), by rw [eF]; exact hf.1,
      by rw [eF]; exact ai.four⟩
    (covers_append (Lay.covers wi (sepB_bounds hs).2) (covers_wr cw)) cw fun s' hk hq => hQ s' hk ?_
  simp only [kEnc, mkK, Encode12.E, eF, eO, State.withRegions_mem, State.callEntry_mem, hf.2] at hq; exact hq

/-! ## `vg_mlkem_compress_encode`, `vg_mlkem_decode_decompress` -/

def kCmp : Contract isa := mkK CompressEncode.Pre
  (fun s₀ s => bytesAt s.mem (CompressEncode.O s₀) (CompressEncode.L s₀) = CompressEncode.E s₀)
  (regsEq [.a0, .a1, .a2, .a3])

theorem kCmp_ok : ∀ s, kCmp.pre s → ∃ t s', Exec isa Impl.MlKem.RISCV64.compressEncode s t s' ∧
    abiPreserved s s' ∧ kCmp.post s s' :=
  mkK_ok fun _ hp => WP.mono (CompressEncode.correct hp) fun _ ⟨h1, h2, h3, h⟩ =>
    ⟨h1, h2, h3, bytesAt_eq! (compressEncode_length _ _ ▸ hp.len.symm) h⟩

def kDcm : Contract isa := mkK DecodeDecompress.Pre
  (fun s₀ s => PolyIs s.mem (DecodeDecompress.F s₀) (DecodeDecompress.D s₀)) (regsEq [.a0, .a1, .a2, .a3])

theorem kDcm_ok : ∀ s, kDcm.pre s → ∃ t s', Exec isa Impl.MlKem.RISCV64.decodeDecompress s t s' ∧
    abiPreserved s s' ∧ kDcm.post s s' :=
  mkK_ok fun s₀ hp => WP.mono (DecodeDecompress.correct hp) fun _ ⟨h1, h2, h3, h⟩ =>
    ⟨h1, h2, h3, polyIs_of_coeffAt (p := DecodeDecompress.F s₀) fun j hj => by
      rw [h j (by rw [VG.Proof.MlKem.n_eq] at hj; exact hj)]; rfl⟩

theorem width_lt {d : Nat} (hd : d ∈ compressWidths) : d < 2 ^ 32 ∧ 32 * d < 2 ^ 32 := by
  rcases VG.Proof.MlKem.mem_compressWidths hd with rfl | rfl | rfl <;> decide

theorem dN_eq {d : Nat} (h : d < 2 ^ 32) : ((BitVec.ofNat 64 d).setWidth 32).toNat = d := by
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : d < 2 ^ 64), Nat.mod_eq_of_lt h]

theorem len_eq {d : Nat} (h : d < 2 ^ 32) : (BitVec.ofNat 64 d).toNat = d := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

/-- `ByteEncode_d(Compress_d(f))` of the polynomial at `(i, o)` into the `32 d` bytes at `(j, o')`. -/
theorem compressL {L : Lay} {s : State} (hL : L.Ok) {i o j o' d : Nat}
    (g3 : s.gpr .a0 = L.A i o) (g4 : s.gpr .a1 = BitVec.ofNat 64 d)
    (g5 : s.gpr .a2 = L.A j o') (g6 : s.gpr .a3 = BitVec.ofNat 64 (32 * d))
    (hd : d ∈ compressWidths) (hs : sepB L.sizes (i, o, 1024) (j, o', 32 * d) = true)
    (wi : L.buf i ∈ s.rd ++ s.wr) (wj : L.buf j ∈ s.wr) {f : Poly} (hf : PolyIs s.mem (L.A i o) f)
    (ai : L.Al i o) {Q : State → Prop}
    (hQ : ∀ s', Kept (L.RL [(j, o', 32 * d)]) s s' → bytesAt s'.mem (L.A j o') (32 * d) = compressEncode d f →
      Q s') :
    WP isa callCompress s Q := by
  have ⟨d1, d2⟩ := width_lt hd
  have hd0 : 0 < 32 * d := by rcases VG.Proof.MlKem.mem_compressWidths hd with rfl | rfl | rfl <;> decide
  let V := view s [polyRegion (L.A i o)] [⟨L.A j o', 32 * d⟩]
  have eF : CompressEncode.F V = L.A i o := by simp only [V, CompressEncode.F, view_r3, g3]
  have eO : CompressEncode.O V = L.A j o' := by simp only [V, CompressEncode.O, view_r5, g5]
  have eD : CompressEncode.dN V = d := by simp only [V, CompressEncode.dN, view_r4, g4, dN_eq d1]
  have eL : CompressEncode.L V = 32 * d := by simp only [V, CompressEncode.L, view_r6, g6, len_eq d2]
  have cw : Covers [⟨L.A j o', 32 * d⟩] s.wr := Lay.covers wj (sepB_bounds (sepB_symm hs)).2
  have hpre : CompressEncode.Pre V :=
    ⟨by simp only [V, eF, State.withRegions_rd], by simp only [V, CompressEncode.outR, eO, eL, State.withRegions_wr],
      by simp only [CompressEncode.outR, eF, eO, eL]; exact Lay.disj hL hs,
      by rw [eF]; exact Lay.fitB hL (sepB_bounds hs) (by decide),
      by rw [eO, eL]; exact Lay.fitB hL (sepB_bounds (sepB_symm hs)) hd0,
      by rw [eD]; exact hd, by rw [eL, eD], by rw [eF]; exact hf.1, by rw [eF]; exact ai.four⟩
  refine call_kept (k := kCmp) kCmp_ok (by decide +kernel) (rd := [polyRegion (L.A i o)])
    (wr := [⟨L.A j o', 32 * d⟩]) hpre
    (covers_append (Lay.covers wi (sepB_bounds hs).2) (covers_wr cw)) cw fun s' hk hq => hQ s' hk ?_
  have hq' : bytesAt (s'.withRegions _ _).mem (CompressEncode.O V) (CompressEncode.L V) = CompressEncode.E V := hq
  simp only [CompressEncode.E, CompressEncode.P, eF, eO, eL, eD, State.withRegions_mem, V,
    State.callEntry_mem, hf.2] at hq'
  exact hq'

/-- `Decompress_d(ByteDecode_d(·))` of the `32 d` bytes at `(i, o)` into the polynomial at `(j, o')`. -/
theorem decompressL {L : Lay} {s : State} (hL : L.Ok) {i o j o' d : Nat}
    (g3 : s.gpr .a0 = L.A i o) (g4 : s.gpr .a1 = BitVec.ofNat 64 (32 * d))
    (g5 : s.gpr .a2 = BitVec.ofNat 64 d) (g6 : s.gpr .a3 = L.A j o')
    (hd : d ∈ compressWidths) (hs : sepB L.sizes (i, o, 32 * d) (j, o', 1024) = true)
    (wi : L.buf i ∈ s.rd ++ s.wr) (wj : L.buf j ∈ s.wr) (aj : L.Al j o') {Q : State → Prop}
    (hQ : ∀ s', Kept (L.RL [(j, o', 1024)]) s s' →
      PolyIs s'.mem (L.A j o') (decodeDecompress d (bytesAt s.mem (L.A i o) (32 * d))) → Q s') :
    WP isa callDecompress s Q := by
  have ⟨d1, d2⟩ := width_lt hd
  have hd0 : 0 < 32 * d := by rcases VG.Proof.MlKem.mem_compressWidths hd with rfl | rfl | rfl <;> decide
  let V := view s [⟨L.A i o, 32 * d⟩] [polyRegion (L.A j o')]
  have eB : DecodeDecompress.B V = L.A i o := by simp only [V, DecodeDecompress.B, view_r3, g3]
  have eF : DecodeDecompress.F V = L.A j o' := by simp only [V, DecodeDecompress.F, view_r6, g6]
  have eD : DecodeDecompress.dN V = d := by simp only [V, DecodeDecompress.dN, view_r5, g5, dN_eq d1]
  have eL : DecodeDecompress.L V = 32 * d := by simp only [V, DecodeDecompress.L, view_r4, g4, len_eq d2]
  have cw : Covers [polyRegion (L.A j o')] s.wr := Lay.covers wj (sepB_bounds (sepB_symm hs)).2
  have hpre : DecodeDecompress.Pre V :=
    ⟨by simp only [V, DecodeDecompress.inR, eB, eL, State.withRegions_rd], by simp only [V, eF, State.withRegions_wr],
      by simp only [DecodeDecompress.inR, eB, eF, eL]; exact Lay.disj hL hs,
      by rw [eB, eL]; exact Lay.fitB hL (sepB_bounds hs) hd0,
      by rw [eF]; exact Lay.fitB hL (sepB_bounds (sepB_symm hs)) (by decide),
      by rw [eD]; exact hd, by rw [eL, eD], by rw [eF]; exact aj.four⟩
  refine call_kept (k := kDcm) kDcm_ok (by decide +kernel) (rd := [⟨L.A i o, 32 * d⟩])
    (wr := [polyRegion (L.A j o')]) hpre
    (covers_append (Lay.covers wi (sepB_bounds hs).2) (covers_wr cw)) cw fun s' hk hq => hQ s' hk ?_
  have hq' : PolyIs (s'.withRegions _ _).mem (DecodeDecompress.F V) (DecodeDecompress.D V) := hq
  simp only [DecodeDecompress.D, DecodeDecompress.Bl, eB, eF, eL, eD, State.withRegions_mem, V,
    State.callEntry_mem] at hq'
  exact hq'

/-! ## `vg_mlkem_sample_ntt` -/

/-- What `vg_mlkem_sample_ntt` computes, with its loop bounded by 280
iterations: the return value says whether `SampleNTT` finished, and if it
did, `a` holds its result. -/
def kSample : Contract isa := mkK Sample.Pre
  (fun s₀ s => s.gpr .a0 = (if (sampleNTT 280 (Sample.B s₀)).isSome then 1 else 0) ∧
    ∀ a, sampleNTT 280 (Sample.B s₀) = some a → PolyIs s.mem (Sample.A s₀) a)
  (fun a b => regsEq [.a0, .a1, .a2] a b ∧ Sample.B a = Sample.B b)

theorem kSample_ok : ∀ s, kSample.pre s → ∃ t s', Exec isa Impl.MlKem.RISCV64.sampleNTT s t s' ∧
    abiPreserved s s' ∧ kSample.post s s' :=
  mkK_ok fun s₀ hp => WP.mono (Sample.correct hp) fun s h => ⟨h.pres, h.sp, h.ra, by
    by_cases hl : (Sample.Ls s₀ 280).length = 256
    · have e : sampleNTT 280 (Sample.B s₀) = some (VG.Proof.MlKem.toPoly (Sample.Ls s₀ 280)) :=
        VG.Proof.MlKem.sampleNTT_of_full (Nat.le_refl _) (by rw [VG.Proof.MlKem.n_eq]; exact hl)
      refine ⟨by rw [h.a0, ite_eq_left hl, e]; rfl, fun a ha => ?_⟩
      rw [e, Option.some.injEq] at ha; subst ha
      exact Sample.polyAt_toPoly (by rw [VG.Proof.MlKem.n_eq]; exact hl) h.coeff
    · have e : sampleNTT 280 (Sample.B s₀) = none :=
        VG.Proof.MlKem.sampleNTT_none (by rw [VG.Proof.MlKem.n_eq]; exact hl)
      refine ⟨by rw [h.a0, ite_eq_right hl, e]; rfl, fun a ha => ?_⟩
      rw [e] at ha; cases ha⟩

theorem sample_sdepth : sdepth Impl.MlKem.RISCV64.sampleNTT ≤ 1168 := by lit_decide

/-- `SampleNTT` of the seed at `(i, o)` into the polynomial at `(j, o')`,
with the working space at `(k, o'')`. -/
theorem sampleL {L : Lay} {s : State} (hc : Ctx L s) {i o j o' k o'' : Nat}
    (g3 : s.gpr .a0 = L.A i o) (g4 : s.gpr .a1 = L.A j o') (g5 : s.gpr .a2 = L.A k o'')
    (s_ij : sepB L.sizes (i, o, 34) (j, o', 1024) = true) (s_ik : sepB L.sizes (i, o, 34) (k, o'', 2048) = true)
    (s_jk : sepB L.sizes (j, o', 1024) (k, o'', 2048) = true) (s_i1 : sepB L.sizes (i, o, 34) (1, 0, 1168) = true)
    (s_j1 : sepB L.sizes (j, o', 1024) (1, 0, 1168) = true) (s_k1 : sepB L.sizes (k, o'', 2048) (1, 0, 1168) = true)
    (wi : L.buf i ∈ s.rd ++ s.wr) (wj : L.buf j ∈ s.wr) (wk : L.buf k ∈ s.wr) (aj : L.Al j o')
    (ak : L.Al k o'') {Q : State → Prop}
    (hQ : ∀ s', Kept (L.RL [(j, o', 1024), (k, o'', 2048), (1, 0, 1168)]) s s' →
      s'.gpr .a0 = (if (sampleNTT 280 (bytesAt s.mem (L.A i o) 34)).isSome then 1 else 0) →
      (∀ a, sampleNTT 280 (bytesAt s.mem (L.A i o) 34) = some a → PolyIs s'.mem (L.A j o') a) → Q s') :
    WP isa callSample s Q := by
  have hL := hc.ok
  let V := view s [⟨L.A i o, 34⟩] [polyRegion (L.A j o'), ⟨L.A k o'', 2048⟩]
  have eS : Sample.SEED V = L.A i o := by simp only [V, Sample.SEED, view_r3, g3]
  have eA : Sample.A V = L.A j o' := by simp only [V, Sample.A, view_r4, g4]
  have eC : Sample.S V = L.A k o'' := by simp only [V, Sample.S, view_r5, g5]
  have eb : Sample.STK V = L.R 1 0 1168 := hc.bel
  have eBv : Sample.B V = bytesAt s.mem (L.A i o) 34 := by
    show bytesAt s.mem (Sample.SEED V) 34 = _
    rw [eS]
  have cw : Covers [polyRegion (L.A j o'), ⟨L.A k o'', 2048⟩] s.wr :=
    covers_cons' (Lay.covers wj (sepB_bounds s_jk).2) (covers_cons' (Lay.covers wk (sepB_bounds (sepB_symm s_ik)).2)
      covers_nil')
  have hpre : Sample.Pre V := by
    refine ⟨hc.al, hc.sp1168, by simp only [V, eS, State.withRegions_rd], by simp only [V, eA, eC, State.withRegions_wr],
      by rw [eS, eA]; exact Lay.disj hL s_ij, by rw [eS, eC]; exact Lay.disj hL s_ik,
      by rw [eA, eC]; exact Lay.disj hL s_jk, by rw [eb, eS]; exact Lay.disj hL (sepB_symm s_i1),
      by rw [eb, eA]; exact Lay.disj hL (sepB_symm s_j1), by rw [eb, eC]; exact Lay.disj hL (sepB_symm s_k1),
      by rw [eS]; exact Lay.fitB hL (sepB_bounds s_ij) (by decide),
      by rw [eA]; exact Lay.fitB hL (sepB_bounds s_jk) (by decide),
      by rw [eC]; exact Lay.fitB hL (sepB_bounds (sepB_symm s_ik)) (by decide), by rw [eA]; exact aj.four,
      by rw [eC]; exact ak⟩
  refine Proof.Sha3.RISCV64.Stream.call1168 (k := kSample) kSample_ok sample_sdepth hpre
    (covers_append (Lay.covers wi (sepB_bounds s_ij).2) (covers_wr cw)) cw
    fun s' hrd hwr hsp hf hcs hq => hQ s' ⟨hcs, hsp, hrd, hwr, ?_⟩ ?_ ?_
  · rw [hc.bel] at hf; exact hf
  · have h1 : s'.gpr .a0 = _ := hq.1
    rw [eBv] at h1; exact h1
  · intro a ha
    have h2 : PolyIs s'.mem (Sample.A V) a := hq.2 a (by rw [eBv]; exact ha)
    rw [eA] at h2; exact h2

end VG.Proof.MlKem.RISCV64
