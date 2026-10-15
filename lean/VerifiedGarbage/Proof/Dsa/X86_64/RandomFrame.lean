module

public import VerifiedGarbage.Impl.Dsa.X86_64.Random
public import VerifiedGarbage.Proof.Bignum.X86_64.Words
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.Framework.Omega

/-! Accesses to the randomized-signing frame. -/
@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

theorem random_ea_sp (s : State) (d : Nat) : s.ea (Random.sp d) = off (s.gpr .rsp) d := by
  simp only [State.ea, Random.sp, BitVec.ofInt_natCast, off]

theorem random_ea_base (s : State) (r : Reg) : s.ea { base := r } = s.gpr r := by
  simp only [State.ea, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero]

theorem random_rangeInit_ok {s : State} {B q : Addr} {l n : Nat}
    (hs : Scr s B Random.frameBytes) (hsp : s.gpr .rsp = B)
    (hl : word s.mem B Random.oQLen = BitVec.ofNat 64 l)
    (hn : word s.mem B Random.oWidth = BitVec.ofNat 64 n)
    (hq : word s.mem B Random.oQ = q) :
    WP isa (.block Random.rangeInit) s fun t =>
      t.gpr .rdx = off B (Random.oNonce + l) ∧
      t.gpr .r10 = q + BitVec.ofNat 64 n ∧ t.gpr .r11 = BitVec.ofNat 64 n ∧
      t.gpr .r8 = 0 ∧ t.gpr .r9 = 0 ∧ t.mem = s.mem ∧
      Keep [.rdx, .r10, .r11, .r8, .r9] s t := by
  refine WP.mono (WP.keep [.rdx, .r10, .r11, .r8, .r9] (Q := fun t =>
      t.gpr .rdx = off B (Random.oNonce + l) ∧
      t.gpr .r10 = q + BitVec.ofNat 64 n ∧ t.gpr .r11 = BitVec.ofNat 64 n ∧
      t.gpr .r8 = 0 ∧ t.gpr .r9 = 0 ∧ t.mem = s.mem) ?_ rfl)
    fun _ ⟨⟨hd, hq, hn, h8, h9, hm⟩, hk⟩ => ⟨hd, hq, hn, h8, h9, hm, hk⟩
  unfold Random.rangeInit Random.address
  xrun [List.cons_append, List.nil_append, random_ea_sp, hsp,
    hs.ld (d := Random.oQLen) (by decide), hs.ld (d := Random.oWidth) (by decide),
    hs.ld (d := Random.oQ) (by decide), hl, hn, hq]
  change B + BitVec.ofNat 64 200 + BitVec.ofNat 64 l = B + BitVec.ofNat 64 (200 + l)
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

end VG.Proof.Dsa.X86_64
