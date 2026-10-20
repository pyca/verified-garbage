module

public import VerifiedGarbage.Impl.Ffdh.Arm.CombPrecompute
public import VerifiedGarbage.Proof.Ffdh.Arm.Locals
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
public import VerifiedGarbage.Spec.Rsa.Mont
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeArgs
import VerifiedGarbage.Proof.Bignum.Arm.ExportArray
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Ffdh.Arm.Block

/-! Store a public residue at its canonical comb-table index. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Impl.Ffdh.Arm VG.Impl.Bignum.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Spec.Rsa.Mont (arrAt Layout wOf)
open VG.Proof.X25519.Arm (Rest wp_mov op2_imm)

theorem combStore_ok (s : State) {base ctx : BitVec 32} {len w digit o : Nat}
    (ws : Workspace s base (8*len)) (locals : Locals base len s)
    (layout : Layout s.mem (State.addr base) len) (width : wOf s.mem (State.addr base) = w)
    (ho : o < 8) (ptr : s.gpr .r0 = base)
    (count : s.mem.readW (off (State.addr base) 48) 32 = BitVec.ofNat 32 w)
    (saved : s.mem.readW (off (State.addr s.sp) 4) 32 = ctx)
    (index : s.gpr .r3 = BitVec.ofNat 32 digit)
    (dstFit : (ctx + BitVec.ofNat 32 (24+8*w*(digit+2))).toNat + 8*w ≤ 2^32)
    (write : InRegions s.wr (State.addr (ctx + BitVec.ofNat 32 (24+8*w*(digit+2)))) (8*w))
    (sep : Region.Disjoint ⟨State.addr base,8*len⟩
      ⟨State.addr (ctx + BitVec.ofNat 32 (24+8*w*(digit+2))),8*w⟩) :
    WP isa (CombPrecompute.store o) s fun t =>
      t.mem.read (State.addr (ctx + BitVec.ofNat 32 (24+8*w*(digit+2)))) (8*w) =
        s.mem.read (off (State.addr base) (arrAt w o)) (8*w) ∧
      Frame [⟨State.addr (ctx + BitVec.ofNat 32 (24+8*w*(digit+2))),8*w⟩] s.mem t.mem ∧
      t.gpr .r0 = base ∧ Rest roundClobbers s t := by
  have fit := layout.2.2.1
  rw [width] at fit
  have size : 52 ≤ 8*len := by simp only [arrAt, Spec.Rsa.Mont.hdrBytes] at fit; omega
  rw [CombPrecompute.store, WP.seq_iff, WP.block_append_iff]
  refine WP.mono (combTableArgs_raw_ok s ws locals size ptr count saved index) ?_
  rintro u ⟨⟨output, pu, memU⟩, restU⟩
  rw [combTableAddress] at output
  refine wp_mov (op2_imm (by
    apply encodable_byte
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : o < 2^32)]
    omega)) fun v moved => WP.block_nil ?_
  have restV : Rest roundClobbers u v := moved.rest (by simp [roundClobbers])
  have memV : v.mem = s.mem := moved.mem.trans memU
  refine WP.mono (exportArray_ok v (ws.congr (restV.wr.trans restU.wr))
    (by rw [memV]; exact layout) (by rw [memV]; exact width) ho dstFit
    (by rw [restV.wr, restU.wr]; exact write) sep
    ((moved.other .r0 (by decide)).trans pu) moved.gpr
    ((moved.other .r4 (by decide)).trans output)) ?_
  rintro t ⟨value, frame, pt, _, restT⟩
  rw [memV] at value frame
  exact ⟨value, frame, pt, restU.trans (restV.trans restT)⟩

end VG.Proof.Ffdh.Arm
