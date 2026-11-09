module

-- separate module: API stack-metadata and allocation permissions are independent of the arithmetic and point-validation proofs

public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.PreparePre
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.NormalizeLayout
public import VerifiedGarbage.Proof.Ecdh.AArch64.P521.Contract
public import VerifiedGarbage.Proof.Framework.AArch64.Call
public import VerifiedGarbage.Impl.Weierstrass.AArch64.P521Native.Code
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-! Stack-table freshness follows the existing API's implementation stack
parameter; the old stack-zero specialized precondition cannot supply it. -/

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64

structure PrepareStackPre (s : State) : Prop where
  args : PrepareApiPre s
  room : 3456≤s.sp.toNat
  table_out : Region.Disjoint ⟨s.sp-3456#64,3456⟩ ⟨s.gpr .x0,66⟩
  table_private : Region.Disjoint ⟨s.sp-3456#64,3456⟩ ⟨s.gpr .x1,66⟩
  table_peer : Region.Disjoint ⟨s.sp-3456#64,3456⟩ ⟨s.gpr .x2,133⟩
  table_scratch : Region.Disjoint ⟨s.sp-3456#64,3456⟩ ⟨s.gpr .x3,8192⟩

theorem prepare_stack_pre {s : State}
    (h : (VG.Spec.Ecdh.Instance.exchangeContract VG.Spec.EcKey.P521.inst abi 3456).pre s) :
    PrepareStackPre s := by
  sig_pre [VG.Spec.Ecdh.Instance.exchangeContract,VG.Spec.Ecdh.Instance.exchangeSig,
    VG.Spec.EcKey.P521.inst,VG.Spec.P521.curve,VG.Spec.EcKey.scratchWords,
    VG.AArch64.abi,VG.AArch64.argRegs] at h
  obtain ⟨room,rd,wr,_,_,_,privateApart,peerApart,tOut,tPrivate,tPeer,tScratch,_,_,_,scratchFit⟩ := h
  refine ⟨?_,room,tOut,tPrivate,tPeer,tScratch⟩
  constructor
  · rw [rd,wr]; simp
  · rw [rd,wr]; simp
  · rw [wr]; simp
  · exact privateApart
  · exact peerApart
  · exact scratchFit

theorem PrepareStackPre.tableApart {s : State} (h : PrepareStackPre s) :
    TableWorkspaceApart (s.gpr .x3) (s.sp-3456#64) 8192 := by
  intro d hd
  apply Nat.le_of_not_gt
  intro inside
  have tableContains : (⟨s.sp-3456#64,3456⟩ : Region).Contains (off (s.sp-3456#64) d) 1 :=
    Offset.contains_base _ (by omega_arith) (by omega_arith)
  have workspaceContains : (⟨s.gpr .x3,8192⟩ : Region).Contains (off (s.sp-3456#64) d) 1 := by
    change ofs (s.gpr .x3) (off (s.sp-3456#64) d)+1≤8192
    omega_arith
  exact h.table_scratch _ tableContains workspaceContains

/-- The allocation only adds writable permissions, so the initial API buffer
precondition continues to hold in the actual allocated entry state. -/
theorem PrepareStackPre.allocatedArgs {s : State} (h : PrepareStackPre s) :
    PrepareApiPre (allocated 3456 s) := by
  have p := h.args
  constructor
  · change (⟨s.gpr .x1,66⟩ : Region)∈s.rd++(_::s.wr)
    rcases List.mem_append.mp p.privateRegion with hr|hw
    · exact List.mem_append_left _ hr
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ hw)
  · change (⟨s.gpr .x2,133⟩ : Region)∈s.rd++(_::s.wr)
    rcases List.mem_append.mp p.peer with hr|hw
    · exact List.mem_append_left _ hr
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ hw)
  · exact List.mem_cons_of_mem _ p.scratch
  · exact p.private_apart
  · exact p.peer_apart
  · exact p.scratch_fit

/-- One contiguous allocation supplies all table word permissions, including
those crossing the midpoint that two separate region grants did not cover. -/
theorem PrepareStackPre.tablePtrW {s t : State} (h : PrepareStackPre s)
    (reg : t.gpr .x26=s.sp-3456#64) (wr : t.wr=(allocated 3456 s).wr) :
    PtrW t .x26 (s.sp-3456#64) 3456 := by
  refine ⟨reg,?_,by decide,?_⟩
  · intro d hd
    rw [wr]
    exact ⟨_,by simp [allocated],
      Offset.contains_base _ hd (by omega_arith)⟩
  · rw [BitVec.toNat_sub,BitVec.toNat_ofNat]
    have bound := s.sp.isLt
    have room := h.room
    omega_arith

theorem PrepareStackPre.tablePtr {s t : State} (h : PrepareStackPre s)
    (reg : t.gpr .x26=s.sp-3456#64) (wr : t.wr=(allocated 3456 s).wr) :
    Ptr t .x26 (s.sp-3456#64) 3456 := by
  have p := h.tablePtrW reg wr
  refine ⟨reg,?_,p.enc⟩
  intro d hd
  obtain ⟨r,hr,hc⟩ := p.st d hd
  exact ⟨r,List.mem_append_right _ hr,hc⟩

theorem native_stack_bytes :
    16*VG.Impl.Weierstrass.AArch64.P521Native.exchange.aarch64Depth=3456 := by lit_decide

end VG.Proof.Weierstrass.AArch64.P521Native
