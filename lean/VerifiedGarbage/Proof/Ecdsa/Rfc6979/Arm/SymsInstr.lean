module

public import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Proof.Framework.Arm.Syms
import VerifiedGarbage.Proof.Framework.Block

/-! Preserve symbol addresses alongside the existing instruction-update proofs. -/

@[expose] public section
namespace VG.Proof.Ecdsa.Rfc6979.Arm
open VG VG.Arm VG.Proof.X25519.Arm

structure UpdS (s t : State) (r : Reg) (v : BitVec 32) : Prop extends Upd s t r v where
  syms : t.syms=s.syms

structure MupdS (s t : State) (m : Mem) : Prop extends Mupd s t m where
  syms : t.syms=s.syms

structure FupdS (s t : State) : Prop extends Fupd s t where
  syms : t.syms=s.syms

instance {s t : State} {r : Reg} {v : BitVec 32} : Coe (UpdS s t r v) (Upd s t r v) := ⟨UpdS.toUpd⟩
instance {s t : State} {m : Mem} : Coe (MupdS s t m) (Mupd s t m) := ⟨MupdS.toMupd⟩
instance {s t : State} : Coe (FupdS s t) (Fupd s t) := ⟨FupdS.toFupd⟩

private theorem prefix_syms {i : Instr} {is : List Instr} {s : State} {P Q : State → Prop}
    (one : WP isa (.block [i]) s P)
    (k : ∀ t,P t → t.syms=s.syms → WP isa (.block is) t Q) :
    WP isa (.block (i::is)) s Q := by
  change WP isa (.block ([i]++is)) s Q
  rw [WP.block_append_iff]
  exact WP.mono_syms one k

variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_movS {d : Reg} {o : Op2} {v : BitVec 32} (ho : o.eval s=some v)
    (k : ∀ t,UpdS s t d v → WP isa (.block is) t Q) :
    WP isa (.block (.mov d o::is)) s Q :=
  prefix_syms (wp_mov ho (fun _ u => WP.block_nil u)) (fun _ u sy => k _ ⟨u,sy⟩)

theorem wp_dpS {op : DpOp} {d n : Reg} {o : Op2} {y : BitVec 32} (ho : o.eval s=some y)
    (k : ∀ t,UpdS s t d (dpVal op (s.gpr n) y) → WP isa (.block is) t Q) :
    WP isa (.block (.dp op d n o::is)) s Q :=
  prefix_syms (wp_dp ho (fun _ u => WP.block_nil u)) (fun _ u sy => k _ ⟨u,sy⟩)

theorem wp_movwS {d : Reg} {imm : BitVec 16}
    (k : ∀ t,UpdS s t d (imm.setWidth 32) → WP isa (.block is) t Q) :
    WP isa (.block (.movw d imm::is)) s Q :=
  prefix_syms (wp_movw (fun _ u => WP.block_nil u)) (fun _ u sy => k _ ⟨u,sy⟩)

theorem wp_strS {t n : Reg} {off : Nat} {a : Addr} (ho : off<4096)
    (ha : State.addr (s.gpr n+BitVec.ofNat 32 off)=a) (hw : InRegions s.wr a 4)
    (k : ∀ u,MupdS s u (s.mem.writeW a (s.gpr t)) → WP isa (.block is) u Q) :
    WP isa (.block (.str t n off::is)) s Q :=
  prefix_syms (wp_str ho ha hw (fun _ u => WP.block_nil u)) (fun _ u sy => k _ ⟨u,sy⟩)

theorem wp_cmpS {n : Reg} {o : Op2} {y : BitVec 32} (ho : o.eval s=some y)
    (k : ∀ t,FupdS s t → t.z=(s.gpr n-y==0) → WP isa (.block is) t Q) :
    WP isa (.block (.cmp n o::is)) s Q := by
  refine prefix_syms (P := fun t => Fupd s t ∧ t.z=(s.gpr n-y==0))
    (wp_cmp ho (fun _ u z => WP.block_nil ⟨u,z⟩)) ?_
  exact fun _ ⟨u,z⟩ sy => k _ ⟨u,sy⟩ z

end VG.Proof.Ecdsa.Rfc6979.Arm
