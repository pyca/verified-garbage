module

public import VerifiedGarbage.Impl.Bignum.Arm.CrtCompareProduct
public import VerifiedGarbage.Proof.Bignum.Arm.Workspace
import VerifiedGarbage.Proof.Bignum.Arm.CrtClearWideArgs
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Public pointers and word count for the full CRT product comparison -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest wp_ldr)

theorem crt_comparePointers_ok (s : State) {base a b : BitVec 32} {size : Nat}
    (ws : Workspace s base size) (fit : 244 ≤ size) (ptr : s.gpr .r0 = base)
    (first : s.mem.readW (off (State.addr base) 232) 32 = a)
    (second : s.mem.readW (off (State.addr base) 240) 32 = b) :
    WP isa (.block comparePointers) s fun t => t.gpr .r10 = a ∧ t.gpr .r12 = b ∧
      t.mem = s.mem ∧ Rest [.r10, .r12] s t := by
  unfold comparePointers
  refine wp_ldr (a := off (State.addr base) 232) (by decide)
    (by rw [ptr]; exact addr_add (by have := ws.nowrap; omega)) (ws.read (by omega)) fun u h => ?_
  refine wp_ldr (a := off (State.addr base) 240) (by decide)
    (by rw [h.other .r0 (by decide), ptr]; exact addr_add (by have := ws.nowrap; omega))
    (by rw [h.rd, h.wr]; exact ws.read fit) fun t j => WP.block_nil ?_
  exact ⟨(j.other .r10 (by decide)).trans (h.gpr.trans first),
    by rw [j.gpr, h.mem]; exact second,
    j.mem.trans h.mem, (h.rest (by simp)).trans (j.rest (by simp))⟩

theorem crt_compareArgs_ok (s : State) {base dst a b : BitVec 32} {size w : Nat}
    (ws : Workspace s base size) (fit : 244 ≤ size) (ptr : s.gpr .r0 = base)
    (count : s.mem.readW (off (State.addr base) 48) 32 = BitVec.ofNat 32 w)
    (link : s.mem.readW (off (State.addr base) 236) 32 = dst)
    (first : s.mem.readW (off (State.addr base) 232) 32 = a)
    (second : s.mem.readW (off (State.addr base) 240) 32 = b) :
    WP isa compareArgs s fun t => t.gpr .r0 = dst ∧ t.gpr .r10 = a ∧ t.gpr .r12 = b ∧
      t.gpr .lr = BitVec.ofNat 32 (4 * w + 2) ∧ t.mem = s.mem ∧ Rest [.r0, .r3, .r10, .r12, .lr] s t := by
  rw [compareArgs, WP.seq_iff]
  refine WP.mono (crt_comparePointers_ok s ws fit ptr first second) ?_
  rintro u ⟨firstU, secondU, memU, restU⟩
  refine WP.mono (crt_clearWideArgs_ok u (dst := dst) (w := w) (ws.congr restU.wr) (by omega) (by omega) (by decide)
    ((restU.gpr .r0 (by simp)).trans ptr) (by rw [memU]; exact count) (by rw [memU]; exact link)) ?_
  rintro t ⟨ptrT, countT, _, memT, restT⟩
  exact ⟨ptrT, (restT.gpr .r10 (by simp)).trans firstU, (restT.gpr .r12 (by simp)).trans secondU,
    countT, memT.trans memU, (restU.mono (by simp)).trans (restT.mono (by simp))⟩

end VG.Proof.Bignum.Arm
