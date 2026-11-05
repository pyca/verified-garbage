module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.RefillEntry
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.RefillOutcome
public import VerifiedGarbage.Proof.Dsa.Generation.RefillSearch
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.FrameStore
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Memory
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.AttemptStatus
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.TapeState
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ContextSlice
import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.RsaOaep.X86_64.Mgf
import VerifiedGarbage.Proof.Bignum.Octets

/-! # The refillable-tape search's controller on x86-64

The controller runs one seed per iteration while seeds are rejected. Its
invariant (`LoopInv`): the whole search's result is the search from the
octets `c` it has consumed on, those consumed before it
(`RefillSearch.lean`), and the controller's words hold the pointers to
`used` and `state` and the seeds it may still reject. -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64.Generation.Refill

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64
open VG.Impl.Mgf1.X86_64 (sp)

/-! ## Blocks -/

/-- The start of an iteration: the seed's start into `ctl 3`, and the seeds left tested. -/
theorem iterStart_ok {s : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (L : Lay s F S) (R : Rep s.mem F S V W) (hctl : ctlRegion F ∈ s.wr) (hb : F.toNat + 328 ≤ 2 ^ 64)
    {c n : Nat} (h16 : W 16 = BitVec.ofNat 64 c) (hn : n < 2 ^ 64)
    (h2 : (s.mem.writeW (off F 320) (BitVec.ofNat 64 c)).readW (off F 312) 64 = BitVec.ofNat 64 n) :
    WP isa (.block [.mov .rax (.mem (sp 128)), .store (Impl.Dsa.X86_64.Generation.Refill.ctl 3) .rax,
        .mov .rcx (.mem (Impl.Dsa.X86_64.Generation.Refill.ctl 2)), .alu .test .rcx (.reg .rcx)]) s fun t =>
      t.gpr .rax = BitVec.ofNat 64 c ∧ t.zf = some (decide (n = 0)) ∧
      t.mem = s.mem.writeW (off F 320) (BitVec.ofNat 64 c) ∧ Keep [.rax, .rcx] s t := by
  have cs : Scr s (off F 296) 32 := Scr.of_mem hctl (by
    simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
  have c2 : InRegions (s.rd ++ s.wr) (off F 312) 8 := by simpa [off_off] using cs.ld (d := 16) (by decide)
  have c3 : InRegions s.wr (off F 320) 8 := by simpa [off_off] using cs.st (d := 24) (by decide)
  refine WP.mono (WP.keep [.rax, .rcx] (Q := fun t => t.gpr .rax = BitVec.ofNat 64 c ∧
    t.zf = some (decide (n = 0)) ∧ t.mem = s.mem.writeW (off F 320) (BitVec.ofNat 64 c)) ?_ rfl)
    fun _ ⟨⟨a, b, c⟩, k⟩ => ⟨a, b, c, k⟩
  xrun [Impl.Dsa.X86_64.Generation.Refill.ctl, Impl.Dsa.X86_64.Generation.Refill.frameBytes,
    ea_sp, L.rsp, L.ld (d := 128) (by decide), R.slot (d := 128) (k := 16) rfl (by decide) h16, c2, c3, h2,
    BitVec.and_self, ofNat_beq_zero hn]

/-- The octets left from the seed's start, compared with a seed's. -/
theorem roomCheck_ok {s : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (L : Lay s F S) (R : Rep s.mem F S V W) {c len q : Nat} (hrax : s.gpr .rax = BitVec.ofNat 64 c)
    (h15 : W 15 = BitVec.ofNat 64 len) (hc : c ≤ len) (hl : len < 2 ^ 64) (hq : q < 2 ^ 31) :
    WP isa (.block [.mov .rcx (.mem (sp 120)), .alu .sub .rcx (.reg .rax),
        .alu .cmp .rcx (.imm (BitVec.ofNat 32 q))]) s fun t =>
      t.cf = some (decide (len - c < q)) ∧ t.mem = s.mem ∧ Keep [.rcx] s t := by
  have hsub : BitVec.ofNat 64 len - BitVec.ofNat 64 c = BitVec.ofNat 64 (len - c) := Offset.ofNat_sub_ofNat hc
  refine WP.mono (WP.keep [.rcx] (Q := fun t => t.cf = some (decide (len - c < q)) ∧ t.mem = s.mem) ?_ rfl)
    fun _ ⟨⟨a, b⟩, k⟩ => ⟨a, b, k⟩
  xrun [ea_sp, L.rsp, L.ld (d := 120) (by decide), R.slot (d := 120) (k := 15) rfl (by decide) h15, hrax, hsub,
    sx_ofNat hq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : len - c < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : q < 2 ^ 64)]

/-- The seed's octets at `W 1`, and its witnesses after them. -/
theorem seedStart_ok {s : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (L : Lay s F S) (R : Rep s.mem F S V W) {c q : Nat} {ptr : Addr} (hrax : s.gpr .rax = BitVec.ofNat 64 c)
    (h13 : W 13 = ptr) (hq : q < 2 ^ 31) :
    WP isa (.block (Impl.Dsa.X86_64.Generation.Refill.seedStart q)) s fun t =>
      Lay t F S ∧ Rep t.mem F S V (upd (upd W 1 (off ptr c)) 16 (BitVec.ofNat 64 (c + q))) ∧
      Frame [⟨F, frameBytes⟩] s.mem t.mem ∧ Keep [.rax, .rcx] s t := by
  refine WP.mono (WP.keep [.rax, .rcx] (Q := fun t => t.mem =
      (s.mem.writeW (off F 8) (off ptr c)).writeW (off F 128) (BitVec.ofNat 64 (c + q))) ?_ rfl)
    fun t ⟨hm, kt⟩ => ?_
  · xrun [Impl.Dsa.X86_64.Generation.Refill.seedStart, ea_sp, L.rsp, L.ld (d := 104) (by decide),
      R.slot (d := 104) (k := 13) rfl (by decide) h13, hrax, L.st (d := 8) (by decide), L.st (d := 128) (by decide),
      sx_ofNat hq, off, BitVec.ofNat_add]
  have Rt : Rep t.mem F S V (upd (upd W 1 (off ptr c)) 16 (BitVec.ofNat 64 (c + q))) := by
    rw [hm]; exact (R.wf L.geo (k := 1) (by decide) _).wf L.geo (k := 16) (by decide) _
  refine ⟨lay_of_rep L R Rt (by simp [upd]) (kt.gpr (by decide)) kt.2.2, Rt, ?_, kt⟩
  rw [hm]
  exact (frameWord_write (k := 1) (by decide) _ _).writeW (List.mem_singleton_self _) _
    (Offset.contains_base F (d := 128) (by decide) (by decide))

/-- A rejected seed: one fewer left. -/
theorem rejected_ok {s : State} {F : Addr} (hsp : s.gpr .rsp = F) (hctl : ctlRegion F ∈ s.wr)
    (hb : F.toNat + 328 ≤ 2 ^ 64) {n : Nat} (hn : n + 1 < 2 ^ 64)
    (h2 : s.mem.readW (off F 312) 64 = BitVec.ofNat 64 (n + 1)) :
    WP isa (.block Impl.Dsa.X86_64.Generation.Refill.rejected) s fun t =>
      t.mem = s.mem.writeW (off F 312) (BitVec.ofNat 64 n) ∧ Keep [.rax] s t := by
  have cs : Scr s (off F 296) 32 := Scr.of_mem hctl (by
    simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
  have c2 : InRegions s.wr (off F 312) 8 := by simpa [off_off] using cs.st (d := 16) (by decide)
  have c2' : InRegions (s.rd ++ s.wr) (off F 312) 8 := by simpa [off_off] using cs.ld (d := 16) (by decide)
  have e : BitVec.ofNat 64 (n + 1) - 1 = BitVec.ofNat 64 n := by
    rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, Offset.ofNat_sub_ofNat (by omega)]
    rfl
  refine WP.keep [.rax] ?_ rfl
  xrun [Impl.Dsa.X86_64.Generation.Refill.rejected, Impl.Dsa.X86_64.Generation.Refill.ctl,
    Impl.Dsa.X86_64.Generation.Refill.frameBytes, ea_sp, hsp, c2, c2', h2]
  rw [e]

end VG.Proof.Dsa.X86_64.Generation.Refill
