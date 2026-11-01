module

public import VerifiedGarbage.Proof.Bignum.Arm.WindowKernel
public import VerifiedGarbage.Impl.Bignum.Arm.CrtNarrowPower
import VerifiedGarbage.Proof.Bignum.Arm.WindowPhase
public import VerifiedGarbage.Impl.Bignum.Arm.CrtLayout
import VerifiedGarbage.Proof.Bignum.Arm.ExpControls
public import VerifiedGarbage.Proof.Bignum.Arm.PublicBuffers
public import VerifiedGarbage.Proof.Bignum.Arm.ExpPhaseInput
import VerifiedGarbage.Proof.Bignum.Arm.Stack
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! # The private exponentiation in the narrow workspace -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt arrAt)
open VG.Proof.X25519.Arm (Rest)

/-- A prepared narrow workspace holding the reduced input, and the exponent's saved argument. -/
structure NarrowExpInput (base ep : BitVec 32) (len v M x eLen es : Nat) (eb : List Byte) (s : State) : Prop where
  ready : ArithmeticReady base len v s
  modulus : numAt s.mem (State.addr base) v 0 = M
  odd : M % 2 = 1
  input : numAt s.mem (State.addr base) v 1 = x
  r2 : numAt s.mem (State.addr base) v 4 = 2 ^ (128 * v) % M
  stackFit : s.sp.toNat + es + 8 ≤ 2 ^ 32
  slotSmall : es + 4 < 4096
  pointerRead : InRegions (s.rd ++ s.wr) (off (State.addr s.sp) es) 4
  countRead : InRegions (s.rd ++ s.wr) (off (State.addr s.sp) (es + 4)) 4
  pointer : s.mem.readW (off (State.addr s.sp) es) 32 = ep
  count : s.mem.readW (off (State.addr s.sp) (es + 4)) 32 = BitVec.ofNat 32 eLen
  exponent : PublicBytes ep eLen eb s
  separate : Region.Disjoint ⟨State.addr ep, eLen⟩ ⟨State.addr base, 8 * len⟩
  positive : 0 < eLen
  fits : eLen < 2 ^ 32
  /-- Room for the windowed exponentiation's table after the eight arrays. -/
  tableFits : arrAt v 16 ≤ 8 * len

/-- A narrow workspace of a width at most the modulus's has room for the table. -/
theorem table_fits {v W : Nat} (h : v ≤ W) : arrAt v 16 ≤ 8 * workspaceWords W := by
  simp only [arrAt, Proof.Rsa.Mont.hdrBytes, workspaceWords]
  omega

theorem crt_exponentArgs_ok (s : State) {base ep : BitVec 32} {len v M x eLen es : Nat} {eb : List Byte}
    (h : NarrowExpInput base ep len v M x eLen es eb s) :
    WP isa (.block (exponentArgs es)) s fun t =>
      t.gpr .r1 = ep ∧ t.gpr .r2 = BitVec.ofNat 32 eLen ∧ t.mem = s.mem ∧ Rest [.r1, .r2] s t := by
  have small := h.slotSmall
  unfold exponentArgs
  refine wp_loadStack (a := off (State.addr s.sp) es) (by omega)
    (addr_add (by have := h.stackFit; omega)) h.pointerRead fun u a => ?_
  refine wp_loadStack (a := off (State.addr s.sp) (es + 4)) (by omega)
    (by rw [a.sp]; exact addr_add (by have := h.stackFit; omega)) (by rw [a.rd, a.wr]; exact h.countRead)
    fun t b => WP.block_nil ?_
  exact ⟨by rw [b.other .r1 (by decide), a.gpr, h.pointer], by rw [b.gpr, a.mem, h.count],
    b.mem.trans a.mem, (a.rest (by decide)).trans (b.rest (by decide))⟩

theorem NarrowExpInput.of_mem {s t : State} {base ep : BitVec 32} {len v M x eLen es : Nat} {eb : List Byte}
    (h : NarrowExpInput base ep len v M x eLen es eb s) (mem : t.mem = s.mem) (rest : Rest [.r1, .r2] s t) :
    NarrowExpInput base ep len v M x eLen es eb t := by
  refine ⟨h.ready.of_mem mem rest ((rest.gpr .r0 (by decide)).trans h.ready.ptr), by rw [mem]; exact h.modulus, h.odd,
    by rw [mem]; exact h.input, by rw [mem]; exact h.r2, by rw [rest.sp]; exact h.stackFit, h.slotSmall,
    by rw [rest.rd, rest.wr, rest.sp]; exact h.pointerRead, by rw [rest.rd, rest.wr, rest.sp]; exact h.countRead,
    by rw [mem, rest.sp]; exact h.pointer, by rw [mem, rest.sp]; exact h.count,
    h.exponent.after_frame (regions := []) (by rw [mem]; exact Frame.refl _ _) rest (by simp),
    h.separate, h.positive, h.fits, h.tableFits⟩

theorem crt_narrowControls_ready (s : State) {base ep : BitVec 32} {len v M x eLen es : Nat} {eb : List Byte}
    (h : NarrowExpInput base ep len v M x eLen es eb s)
    (pointerR : s.gpr .r1 = ep) (countR : s.gpr .r2 = BitVec.ofNat 32 eLen) :
    WP isa (.block expControls) s fun t =>
      ExpPhaseInput base ep len v M x eb t ∧ Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧
      Rest roundClobbers s t := by
  refine WP.mono (expControls_ok s h.ready) ?_
  rintro t ⟨ready, pointer, count, arrays, frame, rest⟩
  have restT : Rest roundClobbers s t := rest.mono (by decide)
  have exponent := h.exponent.after_frame frame restT
    (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact h.separate)
  have positive : 0 < M := by have := h.ready.modulus; rw [h.modulus] at this; omega
  have r2 := (arrays 4 (by decide)).trans h.r2
  refine ⟨⟨ready, (arrays 0 (by decide)).trans h.modulus, h.odd, (arrays 1 (by decide)).trans h.input,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, exponent.byte⟩, frame, restT⟩
  · rw [r2]; exact Nat.mod_lt _ positive
  · rw [r2, Nat.mod_mod, ← Nat.pow_add, show 64 * v + 64 * v = 128 * v by omega]
  · rw [pointer, pointerR]
  · rw [count, countR, exponent.length]
  · rw [exponent.length]; exact h.positive
  · rw [exponent.length]; exact h.fits
  · rw [exponent.length]; exact exponent.fits
  · rw [exponent.length]; exact exponent.read
  · rw [exponent.length]; exact h.separate

theorem crt_narrowExp_ok (s : State) {base ep : BitVec 32} {len v M x eLen es : Nat} {eb : List Byte}
    (h : NarrowExpInput base ep len v M x eLen es eb s) (kernel : WindowKernel := baselineWindowKernel) :
    WP isa ((narrowExpWith kernel.code) es) s fun t => ArithmeticReady base len v t ∧
      numAt t.mem (State.addr base) v 6 = Spec.Rsa.powMod x (Spec.Rsa.os2ip eb) M ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [narrowExpWith, WP.seq_iff]
  refine WP.mono (crt_exponentArgs_ok s h) ?_
  rintro u ⟨pointerU, countU, memU, restU⟩
  rw [WP.seq_iff]
  refine WP.mono (crt_narrowControls_ready u (h.of_mem memU restU) pointerU countU) ?_
  rintro z ⟨input, frameZ, restZ⟩
  refine WP.mono (kernel.correct z input h.tableFits) ?_
  rintro t ⟨ready, value, _, _, _, frameT, restT⟩
  rw [memU] at frameZ
  exact ⟨ready, value, frameZ.trans frameT, (restU.mono (by decide)).trans (restZ.trans restT)⟩

end VG.Proof.Bignum.Arm
