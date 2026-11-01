module

public import VerifiedGarbage.Proof.Framework.RISCV64.Steps
public import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad
public import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad64
public import VerifiedGarbage.Proof.Framework.Bswap
public import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Proof.Cmac.Mem
import VerifiedGarbage.Proof.AesCcm.Words
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.RISCV64.Exec

/-!
# RISC-V: big-endian doublewords a byte at a time

Untrusted: everything here is checked by Lean. `loadBE64` loads the
doubleword at an address byte-reversed (`be64_eq`, `wp_loadBE64`), and
`storeBE 8` stores one byte-reversed (`writeBytes_beBytes`, `wp_storeBE8`),
as a doubleword `ld` or `sd` of `byteRev64` would, at any alignment.
-/

@[expose] public section

namespace VG.RISCV64.BE64

open VG VG.RISCV64 VG.RISCV64.Steps VG.WriteBytes


/-- `storeBE 8` stores the bytes of the byte-reversed word, least
significant first. -/
theorem beBytes_eq (x : BitVec 64) : ByteLoad.beBytes 8 x = Proof.Cmac.le8 (byteRev64 x) := by
  simp only [ByteLoad.beBytes, Proof.Cmac.le8]
  refine List.map_congr_left fun j hj => ?_
  have hj8 : j < 8 := List.mem_range.mp hj
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_setWidth, BitVec.getLsbD_extractLsb', byteRev64_getLsbD _ (by omega),
    BitVec.getLsbD_ushiftRight]
  simp only [hi, decide_true, Bool.true_and]
  congr 1
  omega

/-- What `storeBE 8` writes is the byte-reversed word. -/
theorem writeBytes_beBytes (m : Mem) (a : Addr) (x : BitVec 64) :
    writeBytes m a (ByteLoad.beBytes 8 x) = m.writeW a (byteRev64 x) := by
  rw [beBytes_eq, Proof.AesCcm.writeW64_eq]

/-- What `loadBE64` loads is the byte-reversed doubleword. -/
theorem be64_eq (m : Mem) (p : Addr) (off : Nat) :
    ByteLoad.be64 m p off = byteRev64 (m.readW (p + BitVec.ofNat 64 off) 64) := by
  have e : ∀ k, p + BitVec.ofNat 64 (off + k) = p + BitVec.ofNat 64 off + BitVec.ofNat 64 k := fun k => by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  have o : ∀ k, p + BitVec.ofNat 64 off + BitVec.ofNat 64 (k + 1) = p + BitVec.ofNat 64 off + BitVec.ofNat 64 k + 1 :=
    fun k => by rw [BitVec.add_assoc (p + _), BitVec.ofNat_add]; rfl
  rw [byteRev64_readW]
  simp only [ByteLoad.be64, e, o, BitVec.add_zero]

theorem wp_li_int {is : List Instr} {s : State} {Q : State → Prop} {d : Reg} {imm : Int} (h : imm12 imm)
    (k : ∀ s', Upd s s' d (BitVec.ofInt 64 imm) → WP isa (.block is) s' Q) :
    WP isa (.block (.li d imm :: is)) s Q :=
  WP.cons (exec_li h) (k _ (Upd.write _ _ _))

/-- `storeBE 8 v tmp n off`: the doubleword `v` byte-reversed at `a`, and
`tmp` then `v`. -/
theorem wp_storeBE8 {is : List Instr} {s : State} {Q : State → Prop} {v tmp n : Reg} {off : Nat} {a : Addr}
    (htv : tmp ≠ v) (htn : tmp ≠ n) (ho : off + 8 ≤ 2048) (ha : s.gpr n + BitVec.ofNat 64 off = a)
    (hout : InRegions s.wr a 8)
    (k : ∀ s₁ s', Mupd s s₁ (s.mem.writeW a (byteRev64 (s.gpr v))) → Upd s₁ s' tmp (s.gpr v) →
      WP isa (.block is) s' Q) :
    WP isa (.block (Impl.Words.RISCV64.storeBE 8 v tmp n off ++ is)) s Q := by
  rw [WP.block_append_iff]
  have hin : InRegions s.wr (s.gpr n + BitVec.ofNat 64 off) 8 := by rw [ha]; exact hout
  refine WP.mono (ByteLoad.storeBE_ok htv htn (by decide) (by decide) ho
    (fun j hj => ByteLoad.in_byte' hin hj)) fun s' e => ?_
  subst e
  rw [writeBytes_beBytes, ha]
  exact k { s with mem := s.mem.writeW a (byteRev64 (s.gpr v)) } _ ⟨rfl, rfl, rfl, rfl, rfl⟩ (Upd.write _ _ _)

/-- `loadBE64 d tmp n off`: the doubleword at `a` byte-reversed in `d`. -/
theorem wp_loadBE64 {is : List Instr} {s : State} {Q : State → Prop} {d tmp n : Reg} {off : Nat} {a : Addr}
    (hdn : d ≠ n) (htn : tmp ≠ n) (hdt : d ≠ tmp) (ho : off + 7 < 2048) (ha : s.gpr n + BitVec.ofNat 64 off = a)
    (hin : InRegions (s.rd ++ s.wr) a 8)
    (k : ∀ s₁ s', Upd s s₁ tmp ((s.mem (s.gpr n + BitVec.ofNat 64 (off + 7))).setWidth 64) →
      Upd s₁ s' d (byteRev64 (s.mem.readW a 64)) → WP isa (.block is) s' Q) :
    WP isa (.block (Impl.Words.RISCV64.loadBE64 d tmp n off ++ is)) s Q := by
  rw [WP.block_append_iff]
  refine WP.mono (ByteLoad.loadBE64_ok hdn htn hdt ho (by rw [ha]; exact hin)) fun s' e => ?_
  subst e
  rw [be64_eq, ha]
  exact k _ _ (Upd.write _ _ _) (Upd.write _ _ _)


end VG.RISCV64.BE64
