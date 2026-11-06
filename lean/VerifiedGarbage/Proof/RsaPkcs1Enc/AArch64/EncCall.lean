module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.EncLoops
public import VerifiedGarbage.Proof.Framework.AArch64.Call
public import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.Callee
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# RSAES-PKCS1-v1_5 encryption on AArch64: the call

Once `PS` and `M` are copied, the frame holds
`EM = 0x00 ‖ 0x02 ‖ PS ‖ 0x00 ‖ M` (`em_bytes`). `callArgs` sets the call's
`input` and `input_len` (`CallReady`); after the call, whatever it wrote to
`out`, `Ctx` holds again (`CalledF`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.AArch64.Enc

open VG VG.AArch64 VG.Impl.RsaPkcs1Enc.AArch64.Encrypt

theorem bytesAt_add (m : Mem) (p : Addr) (a b : Nat) :
    Spec.Rsa.bytesAt m p (a + b) = Spec.Rsa.bytesAt m p a ++ Spec.Rsa.bytesAt m (p + BitVec.ofNat 64 a) b := by
  simp only [Spec.Rsa.bytesAt, List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp, add_add]

/-- The bytes at `p`, each given. -/
theorem bytesAt_eq {m m' : Mem} {p q : Addr} {n : Nat}
    (h : ∀ i < n, m (p + BitVec.ofNat 64 i) = m' (q + BitVec.ofNat 64 i)) :
    Spec.Rsa.bytesAt m p n = Spec.Rsa.bytesAt m' q n := by
  simp only [Spec.Rsa.bytesAt]
  exact List.map_congr_left fun i hi => h i (List.mem_range.mp hi)

/-- The encoded message in the frame. -/
theorem em_bytes {L : Lay} (hL : L.Ok) {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem} {t : State}
    (h : MsgInv L g vv m₀ L.ml.toNat t) :
    Spec.Rsa.bytesAt t.mem (L.Q + BitVec.ofNat 64 oEM) L.k.toNat =
      Spec.RsaPkcs1Enc.encode (Spec.Rsa.bytesAt m₀ L.msg L.ml.toNat) (Spec.Rsa.bytesAt m₀ L.ps L.pl.toNat) := by
  rw [← hL.em_len, show L.pl.toNat + L.ml.toNat + 3 = ((2 + L.pl.toNat) + 1) + L.ml.toNat by omega_arith,
    bytesAt_add, bytesAt_add, bytesAt_add, Spec.RsaPkcs1Enc.encode]
  have e2 : Spec.Rsa.bytesAt t.mem (L.Q + BitVec.ofNat 64 oEM) 2 = [0x00, 0x02] := by
    simp only [Spec.Rsa.bytesAt, List.range_succ, List.range_zero, List.nil_append, List.map_cons,
      List.map_nil, List.cons_append, add_add, Nat.add_zero, h.b0, h.b1]
  have eP : Spec.Rsa.bytesAt t.mem (L.Q + BitVec.ofNat 64 oEM + BitVec.ofNat 64 2) L.pl.toNat =
      Spec.Rsa.bytesAt m₀ L.ps L.pl.toNat :=
    bytesAt_eq fun i hi => by rw [add_add, add_add, ← Nat.add_assoc]; exact h.ps i hi
  have eS : Spec.Rsa.bytesAt t.mem (L.Q + BitVec.ofNat 64 oEM + BitVec.ofNat 64 (2 + L.pl.toNat)) 1 = [0x00] := by
    simp only [Spec.Rsa.bytesAt, List.range_one, List.map_cons, List.map_nil, add_add, Nat.add_zero, ← Nat.add_assoc,
      h.sep]
  have eM : Spec.Rsa.bytesAt t.mem (L.Q + BitVec.ofNat 64 oEM + BitVec.ofNat 64 (2 + L.pl.toNat + 1)) L.ml.toNat =
      Spec.Rsa.bytesAt m₀ L.msg L.ml.toNat :=
    bytesAt_eq fun i hi => by
      rw [add_add, add_add, show oEM + (2 + L.pl.toNat + 1 + i) = oEM + 3 + L.pl.toNat + i by omega_arith]
      exact h.msg i hi
  rw [e2, eP, eS, eM]

/-- Before the call. -/
structure CallReady (L : Lay) (g : Reg → BitVec 64) (vv : VReg → BitVec 128) (m₀ : Mem) (t : State) : Prop where
  ctx : Ctx L g vv m₀ t
  x0 : t.gpr .x0 = L.out
  x1 : t.gpr .x1 = L.ol
  x2 : t.gpr .x2 = L.n
  x3 : t.gpr .x3 = L.k
  x4 : t.gpr .x4 = L.e
  x5 : t.gpr .x5 = L.el
  x6 : t.gpr .x6 = L.Q + BitVec.ofNat 64 oEM
  x7 : t.gpr .x7 = L.k
  em : Spec.Rsa.bytesAt t.mem (L.Q + BitVec.ofNat 64 oEM) L.k.toNat =
    Spec.RsaPkcs1Enc.encode (Spec.Rsa.bytesAt m₀ L.msg L.ml.toNat) (Spec.Rsa.bytesAt m₀ L.ps L.pl.toNat)
  z : t.mem.readW (L.Q + BitVec.ofNat 64 oZ) 64 = zmask (Spec.Rsa.bytesAt m₀ L.ps L.pl.toNat)

/-- The registers on entry are the layout's. -/
def RegsOf (L : Lay) (g : Reg → BitVec 64) : Prop :=
  g .x0 = L.out ∧ g .x1 = L.ol ∧ g .x2 = L.n ∧ g .x3 = L.k ∧ g .x4 = L.e ∧ g .x5 = L.el ∧ g .x6 = L.msg ∧
    g .x7 = L.ml

theorem callArgs_inv {L : Lay} (hL : L.Ok) {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem} {t : State}
    (hg : RegsOf L g) (h : MsgInv L g vv m₀ L.ml.toNat t) :
    WP isa (.block callArgs) t (CallReady L g vv m₀) :=
  WP.mono (callArgs_ok t) fun w hw => by
    have go : ∀ r, r ≠ .x6 → r ≠ .x7 → w.gpr r = t.gpr r := hw.other
    refine ⟨h.ctx.regs hw.rd hw.wr hw.sp hw.mem hw.v fun r hr _ => go r (mem_ne hr (by decide))
      (mem_ne hr (by decide)), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [go .x0 (by decide) (by decide), h.x0, hg.1]
    · rw [go .x1 (by decide) (by decide), h.x1, hg.2.1]
    · rw [go .x2 (by decide) (by decide), h.x2, hg.2.2.1]
    · rw [go .x3 (by decide) (by decide), h.x3, hg.2.2.2.1]
    · rw [go .x4 (by decide) (by decide), h.x4, hg.2.2.2.2.1]
    · rw [go .x5 (by decide) (by decide), h.x5, hg.2.2.2.2.2.1]
    · rw [hw.x6, h.ctx.sp]
    · rw [hw.x7, h.x3, hg.2.2.2.1]
    · rw [hw.mem]; exact em_bytes hL h
    · rw [hw.mem]; exact h.z

theorem gpr_ce (t : State) (rd wr : List Region) {r : Reg} (h : r ∉ linkRegs) :
    (t.callEntry.withRegions rd wr).gpr r = t.gpr r := by
  rw [State.withRegions_gpr, State.callEntry_gpr _ h]

theorem stackArg_ce (t : State) (rd wr : List Region) (i : Nat) :
    stackArg (t.callEntry.withRegions rd wr) i = t.mem.readW (t.sp + BitVec.ofNat 64 (8 * i)) 64 := rfl

/-- After the call, whatever it wrote to `out`. -/
structure CalledF (L : Lay) (g : Reg → BitVec 64) (vv : VReg → BitVec 128) (m₀ : Mem) (t' : State) : Prop where
  ctx : Ctx L g vv m₀ t'
  z : t'.mem.readW (L.Q + BitVec.ofNat 64 oZ) 64 = zmask (Spec.Rsa.bytesAt m₀ L.ps L.pl.toNat)

end VG.Proof.RsaPkcs1Enc.AArch64.Enc
