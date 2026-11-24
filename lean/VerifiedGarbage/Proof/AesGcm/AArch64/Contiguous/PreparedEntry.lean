module

public import VerifiedGarbage.Impl.AesGcm.AArch64.Contiguous.Prepared
public import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.Front
public import VerifiedGarbage.Proof.AesGcm.AArch64.Seal
import VerifiedGarbage.Proof.AesGcm.AArch64.OneEntry
import VerifiedGarbage.Proof.Framework.AArch64.LaneRestore
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-! Prepared AES and AES/SHA3 records use the same entry and argument slots.
The saved source and destination remain independent throughout the record. -/

@[expose] public section
namespace VG.Proof.AesGcm.AArch64.Contiguous.Prepared

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64
open VG.Impl.AesGcm.AArch64.Contiguous

abbrev word (W : Addr) (i : Nat) : Addr := W + BitVec.ofNat 64 i
abbrev slotR (W : Addr) (i : Nat) : Region := ⟨word W i,8⟩

structure Entry (wn : Nat) (o t : State) (W : Addr) : Prop where
  env : Env wn (o.gpr .x0) (word W 16) W o.sp t
  x22 : t.gpr .x22 = o.gpr .x1
  x23 : t.gpr .x23 = o.gpr .x2
  x24 : t.gpr .x24 = o.gpr .x3
  x26 : t.gpr .x26 = o.gpr .x3
  x27 : t.gpr .x27 = 0
  x28 : t.gpr .x28 = stackArg o 1
  x4 : t.gpr .x4 = o.gpr .x4
  x5 : t.gpr .x5 = o.gpr .x5
  x6 : t.gpr .x6 = o.gpr .x6
  x7 : t.gpr .x7 = stackArg o 0
  aad : t.mem.readW (word W 216) 64 = o.gpr .x4
  alen : t.mem.readW (word W 224) 64 = o.gpr .x5
  src : t.mem.readW (word W 232) 64 = o.gpr .x6
  len : t.mem.readW (word W 240) 64 = stackArg o 0
  tag : t.mem.readW (word W 248) 64 = stackArg o 1
  dst : t.mem.readW (word W 320) 64 = o.gpr .x7
  saved : SavedAt t.mem W o
  frame : Frame [workR wn W] o.mem t.mem
  rd : t.rd = o.rd
  wr : t.wr = o.wr

private theorem oneEntry_keeps : ∀ r ∈ [Reg.x4,.x5,.x11], (oneEntry 24).all (keepsReg r) = true := by decide

/-- The first three stack words are length, tag, powers. The frame setup
has added the working-space pointer in the fourth word. -/
theorem entry_ok {wn : Nat} {o : State} {W : Addr} (hW : stackArg o 3 = W)
    (access : ∀ i < 4, InRegions (o.rd++o.wr) (stackArgAddr o i) 8)
    (sep : (slotR o.sp 8).Disjoint (workR wn W)) (perm : Perm wn (o.gpr .x0) (word W 16) W o) :
    WP isa (.block preparedArgs) o (Entry wn o · W) := by
  obtain bounds := perm.hWn
  let u := (o.write .x .x11 (o.gpr .x7)).write .x .x7 (stackArg o 0)
  have x (r : Reg) (h7 : r ≠ .x7) (h11 : r ≠ .x11) : u.gpr r = o.gpr r := by simp [u,gpr_write,h7,h11]
  have x7 : u.gpr .x7 = stackArg o 0 := by simp [u,gpr_write]
  have x11 : u.gpr .x11 = o.gpr .x7 := by simp [u,gpr_write]
  have ir := access 0 (by decide)
  change InRegions (o.rd++o.wr) (o.sp+0#64) 8 at ir
  rw [BitVec.add_zero] at ir
  have read : o.mem.read o.sp 8 = stackArg o 0 := by simp [stackArg,stackArgAddr,Mem.readW]
  unfold preparedArgs
  rw [List.append_assoc,List.append_assoc,WP.block_append_iff]
  refine WP.of_runBlock ⟨u,by arun [BitVec.add_zero,ir,read,u],?_⟩
  rw [WP.block_append_iff]
  obtain ⟨trace,a,exec,env,ar,an,al,ac,az,aad,alen,src,n,fr,sav,rd,wr,a6,a7⟩ :=
    oneEntry_args (k := 24) (by decide) (s := u) hW (access 3 (by decide)) (x .x0 (by decide) (by decide)) (perm.of_eq (s' := u) rfl rfl)
  have kept (r : Reg) (hr : r ∈ [Reg.x4,.x5,.x11]) : a.gpr r = u.gpr r := by
    cases exec with | block ex => exact keepsReg_ok (oneEntry_keeps r hr) ex
  refine ⟨trace,a,exec,?_⟩
  have fa : Frame [workR wn W] o.mem a.mem := fr.sub fun r hr =>
    ⟨_,List.mem_singleton_self _,entryR_work W bounds r hr⟩
  have write : InRegions a.wr (word W 320) 8 := in_off env.perm.w (by omega) (by omega)
  let b := {a with mem := a.mem.writeW (word W 320) (o.gpr .x7)}
  have run : runBlock isa [.str .x .x11 .x19 dstO] a = some b := by
    have val := (kept .x11 (by simp)).trans x11
    unfold word at write
    arun [b,word,dstO,env.x19,val,write,Mem.writeW]
  have fb : Frame [slotR W 320] a.mem b.mem :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have fb' : Frame [workR wn W] o.mem b.mem := fa.trans (fb.sub fun r hr =>
    ⟨_,List.mem_singleton_self _, List.mem_singleton.mp hr ▸ (Offset.sub_base W (by omega))⟩)
  change WP isa (.block (_ ++ _)) a _
  rw [WP.block_append_iff]
  refine WP.of_runBlock ⟨b,run,?_⟩
  have tag : b.mem.readW (word b.sp 8) 64 = stackArg o 1 := by
    change b.mem.readW (word a.sp 8) 64 = _
    rw [env.sp]; exact fb'.readW (r := slotR o.sp 8) (Region.contains_self _ _) (by
      simpa only [List.mem_singleton,forall_eq] using sep) (by decide)
  refine (stashArg_ok (Wn := wn) (k := 8) (by decide) (s := b) env.x19 env.perm.w
    (by change InRegions (a.rd++a.wr) (word a.sp 8) 8; rw [rd,wr,env.sp]; exact access 1 (by decide)) tag bounds).mono ?_
  intro t ⟨t28,tm,tg,sp,tr,tw⟩
  have reg (r : Reg) (hr : r ≠ .x10 ∧ r ≠ .x28) : t.gpr r = a.gpr r := tg _ (by simp [hr.1,hr.2])
  have mem : t.mem = (a.mem.writeW (word W 320) (o.gpr .x7)).writeW (word W 248) (stackArg o 1) := tm
  have old (i : Nat) (hi : i+8 ≤ 248) : t.mem.readW (word W i) 64 = a.mem.readW (word W i) 64 := by
    rw [mem]; unfold word
    rw [readW_writeW_other _ _ _ (.inl hi) (by omega) (by decide),
      readW_writeW_other _ _ _ (.inl (by omega)) (by omega) (by decide)]
  have ft : Frame [slotR W 248] b.mem t.mem := by
    rw [tm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine ⟨env.keep (fun r hr => reg r (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hr; rcases hr with rfl|rfl|rfl <;> decide)) sp tr tw,
    (reg _ (by decide)).trans ar,(reg _ (by decide)).trans an,(reg _ (by decide)).trans al,
    (reg _ (by decide)).trans ac,(reg _ (by decide)).trans az,t28,
    (reg _ (by decide)).trans (kept _ (by simp)),(reg _ (by decide)).trans (kept _ (by simp)),
    (reg _ (by decide)).trans a6,(reg _ (by decide)).trans (a7.trans x7),
    (old _ (by decide)).trans aad,(old _ (by decide)).trans alen,(old _ (by decide)).trans src,
    (old _ (by decide)).trans (n.trans x7),?_,?_,?_,?_,tr.trans rd,tw.trans wr⟩
  · rw [mem,Mem.readW_writeW_self64]
  · rw [mem]; unfold word
    rw [readW_writeW_other _ _ _ (.inr (by decide)) (by decide) (by decide),Mem.readW_writeW_self64]
  · have keptSaved : ∀ p ∈ saved, p.1 ≠ .x7 ∧ p.1 ≠ .x11 := by decide
    have sa : SavedAt a.mem W o := fun p hp => (sav p hp).trans (x _ (keptSaved p hp).1 (keptSaved p hp).2)
    have dis {i : Nat} (lo : 216 ≤ i) (hi : i+8 ≤ 2^64) : (savedR W).Disjoint (slotR W i) :=
      Offset.disjoint W (.inl lo) (by decide) hi
    exact (sa.frame fb (by simpa only [List.mem_singleton,forall_eq] using dis (i := 320) (by decide) (by decide))).frame ft
      (by simpa only [List.mem_singleton,forall_eq] using dis (i := 248) (by decide) (by decide))
  · exact fb'.trans (ft.sub fun r hr => ⟨_,List.mem_singleton_self _,
      List.mem_singleton.mp hr ▸ Offset.sub_base W (by omega)⟩)

open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (ctxH blockAt)
open VG.Proof.Gcm.AArch64.Pmull (MulKey)

theorem front_ok {wn : Nat} {o s : State} {W : Addr} (L : Lay wn (o.gpr .x0) (word W 16) W)
    (mul : MulKey) (e : Entry wn o s W) (hn : (o.gpr .x3).toNat = 12) (ha : (o.gpr .x5).toNat ≤ 16)
    (nonce : DataOk wn (word W 16) W o (o.gpr .x2) 12)
    (aad : DataOk wn (word W 16) W o (o.gpr .x4) (o.gpr .x5).toNat) :
    WP isa Impl.AesGcm.AArch64.Fast.front s
      (Fast.FFront wn (o.gpr .x0) (word W 16) W o.sp (ctxH o.mem (o.gpr .x0))
        (bytesAt o.mem (o.gpr .x2) 12) (bytesAt o.mem (o.gpr .x4) (o.gpr .x5).toNat)
        (o.gpr .x6) (stackArg o 0).toNat s) := by
  have size : o.gpr .x3 = BitVec.ofNat 64 12 := by rw [← hn]; simp
  have hh : blockAt s.mem (word (o.gpr .x0) 240) = ctxH o.mem (o.gpr .x0) :=
    blockAt_frame e.frame (by simpa only [List.mem_singleton,forall_eq] using (L.cw'.sub_left (Offset.sub_base (o.gpr .x0) (by decide : 240 + 16 ≤ 256))))
  have j : J0In wn (o.gpr .x0) (word W 16) W o.sp s.gpr (ctxH o.mem (o.gpr .x0)) (o.gpr .x2) 12 s :=
    ⟨e.env,fun _ _ => rfl,e.x23,e.x24.trans size,e.x26.trans size,e.x27,nonce.of_eq e.rd e.wr,hh⟩
  have nonceBytes : bytesAt s.mem (o.gpr .x2) 12 = bytesAt o.mem (o.gpr .x2) 12 :=
    bytesAt_frame e.frame (by simpa only [List.mem_singleton,forall_eq] using nonce.w) (by decide)
  have aadBytes : bytesAt s.mem (o.gpr .x4) (o.gpr .x5).toNat = bytesAt o.mem (o.gpr .x4) (o.gpr .x5).toNat :=
    bytesAt_frame e.frame (by simpa only [List.mem_singleton,forall_eq] using aad.w) (Nat.le_of_lt (o.gpr .x5).isLt)
  rw [← nonceBytes,← aadBytes]
  exact Fast.front_ok L mul j (aad.of_eq e.rd e.wr) ha e.x4 (by simpa using e.x5) e.x6 (by simpa using e.x7)

end VG.Proof.AesGcm.AArch64.Contiguous.Prepared
