module

public import VerifiedGarbage.Proof.Bignum.Arm.CrtLinks
public import VerifiedGarbage.Proof.Bignum.Arm.SetSmallFn
public import VerifiedGarbage.Proof.Bignum.Arm.CrtWorkspaceState
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Initialize the main CRT layout and all five buffer links -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Spec.Rsa.Mont (Layout wOf arrAt)
open VG.Proof.X25519.Arm (Rest)

theorem crt_links_layout {m m' : Mem} {base : BitVec 32} {len w : Nat}
    (h : CrtLayoutState base len w m) (outside : Outside (State.addr base) 224 20 m m') :
    CrtLayoutState base len w m' := by
  have width : wOf m' (State.addr base) = wOf m (State.addr base) :=
    congrArg BitVec.toNat (outside.word (d := 48) (by decide) (by decide))
  refine ⟨?_, width.trans h.width⟩
  unfold Layout
  rw [width]
  refine ⟨h.layout.1, h.layout.2.1, h.layout.2.2.1, ?_⟩
  intro j hj
  change VG.Proof.Mont.word m' (State.addr base) (8 * (8 + j)) = _
  rw [outside.word (by omega) (by omega)]
  exact h.layout.2.2.2 j hj

theorem crt_setupMain_ok (s : State) {base : BitVec 32} {len w : Nat}
    (ws : Workspace s base (8 * len)) (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    (fits : arrAt w 8 ≤ 8 * len) (ptr : s.gpr .r0 = base)
    (count : s.gpr .r7 = BitVec.ofNat 32 w) (zero : s.gpr .r3 = 0) :
    WP isa (.seq setup links) s fun t => CrtMainState base len w t.mem ∧ t.gpr .r0 = base ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [WP.seq_iff]
  refine WP.mono (setup_frame_ok s ws hw hw' fits ptr count zero) ?_
  rintro u ⟨layoutU, widthU, ptrU, frameU, restU⟩
  have stateU : CrtLayoutState base len w u.mem := ⟨layoutU, widthU⟩
  have wsU := ws.congr restU.wr
  refine WP.mono (crt_links_ok u wsU (by have := stateU.size; omega) ptrU (stateU.nativeCount wsU)) ?_
  rintro t ⟨memT, restT⟩
  have result := crtLinkMem_ok u.mem (State.addr base)
    (base + BitVec.ofNat 32 (pOffset w)) (base + BitVec.ofNat 32 (qOffset w))
    (base + BitVec.ofNat 32 (productOffset w)) (base + BitVec.ofNat 32 (compareOffset w))
    (base + BitVec.ofNat 32 (modulusOffset w))
  dsimp only at result
  rw [← memT] at result
  obtain ⟨p, q, product, compare, modulus, outside⟩ := result
  have frameT := outside_workspace outside (size := 8 * len) (by have := stateU.size; omega)
  exact ⟨⟨crt_links_layout stateU outside, p, q, product, compare, modulus⟩,
    (restT.gpr .r0 (by simp)).trans ptrU, frameU.trans frameT,
    restU.trans (restT.mono (by simp [roundClobbers]))⟩

end VG.Proof.Bignum.Arm
