module

public import VerifiedGarbage.Proof.AesGcm.X86_64.DirectGather.Post
public import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.TailPre
import VerifiedGarbage.Proof.AesGcm.X86_64.Fast.TailCT
import VerifiedGarbage.Proof.AesGcm.X86_64.Short.SealFin
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-! Connect the first fused call and the key schedule to the final pair of fragment tails. -/
@[expose] public section
namespace VG.Proof.AesGcm.X86_64.DirectGather
open VG VG.X86_64 Gather Gather.DirectTail Short
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Proof.Gcm.X86_64 (revMask)
open VG.Impl.Gcm.X86_64.Pclmul (poly)
open VG.Spec.Gcm (Block ctxH)

abbrev tailArgs (s : State) : TailArgs :=
  ⟨K s, W s, SP s, Src s, sb s 0, (if 1<Cnt s then sb s 1 else 0), Dst s, sl s 0, L s, (AL s).toNat⟩

namespace Layout
variable {M : CtxMode} {s : State} (h : Layout M s)
include h

theorem ext_apart : ∀ r ∈ changed s, (kR M s).Disjoint r := by
  intro r hr
  simp only [changed, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  exacts [h.k_w, h.k_d, (h.b_k.sub_left (below_sub (by decide) (by decide))).symm]

theorem desc_apart : ∀ r ∈ changed s, (dsR s).Disjoint r := by
  intro r hr
  simp only [changed, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  exacts [h.ds_w, h.ds_d, (h.b_ds.sub_left (below_sub (by decide) (by decide))).symm]

theorem slice_apart {i : Nat} (hi : i < Cnt s) : ∀ r ∈ changed s, (⟨sb s i, sl s i⟩ : Region).Disjoint r := by
  have m := slice_mem s hi
  obtain ⟨d, _, w⟩ := h.ls _ m
  intro r hr
  simp only [changed, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  exacts [w, d, ((h.b_ls _ m).sub_left (below_sub (by decide) (by decide))).symm]

theorem arg_apart : ∀ r ∈ changed s, (argR s).Disjoint r := by
  intro r hr
  simp only [changed, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  exacts [h.w_a.symm, h.d_a.symm, Offset.disjoint_below _ (by decide)]

theorem tail_pre (g : frontGo false s = true) {t : State} {H : Block}
    (e : Env (K s) (W s+16#64) (W s) (SP s) t) (fr : Frame (changed s) s.mem t.mem)
    (rd : t.rd = s.rd) (wr : t.wr = s.wr)
    (data : t.mem.readW (W s+200#64) 64=Dst s) (len : t.mem.readW (W s+192#64) 64=BitVec.ofNat 64 (L s))
    (al : t.mem.readW (W s+184#64) 64=AL s)
    (x0 : t.xmm .xmm0=revMask) (x1 : t.xmm .xmm1=poly) (h1 : IsH1 H (t.xmm .xmm3))
    (h2 : IsH2 H (t.xmm .xmm3) (t.xmm .xmm6)) : TailPre (tailArgs s) H t := by
  obtain ⟨_, cnt, _, bounded⟩ := front_limits (h.front M.ge) g
  have nz : 0 < Cnt s := by omega
  have fl0 : fl s = sl s 0 := by simp [fl_eq, Nat.ne_of_gt nz]
  rw [fl0] at bounded
  have le := (h.front M.ge).le
  rw [fl0] at le
  have rem (pos : 0 < L s - sl s 0) : 1 < Cnt s ∧ sl s 1 = L s - sl s 0 := by
    have gl := h.glen
    rcases cnt with c | c
    · rw [c, gl_succ, gl_zero, Nat.zero_add] at gl; omega
    · rw [c, gl_succ, gl_succ, gl_zero, Nat.zero_add] at gl; omega
  have lc : L s < 2^64 := BitVec.isLt _
  have src0 := slice_mem s nz
  have sw := h.ls _ src0
  have c := h.oneCtx M.ge
  have ds : Covers [dsR s] (t.rd++t.wr) := by rw [rd, wr, h.rd]; exact covers_of_mem (by simp)
  have sc (i : Nat) (hi : i<Cnt s) : Covers [⟨sb s i,sl s i⟩] (t.rd++t.wr) := by
    rw [rd, wr, h.rd]; exact covers_of_mem (by simp [slice_mem s hi])
  have dsub : (tailArgs s).outR.Sub (dR s) := Offset.sub_base _ (by change 16*(sl s 0/16)+(L s-16*(sl s 0/16)) ≤ L s; omega)
  have ssub : (tailArgs s).firstR.Sub ⟨sb s 0,sl s 0⟩ := Offset.sub_base _ (by change 16*(sl s 0/16)+sl s 0%16 ≤ sl s 0; omega)
  have d0 : (dsR s).Contains (Src s) 8 := by
    simpa using Offset.contains_base (Src s) (k := Cnt s*16) (d := 0) (n := 8) (by omega) (by decide)
  have d8 : (dsR s).Contains (Src s+8#64) 8 := Offset.contains_base _ (d := 8) (by omega) (by decide)
  have d16 (hp : 0<L s-sl s 0) : (dsR s).Contains (Src s+16#64) 8 :=
    Offset.contains_base _ (d := 16) (by have := (rem hp).1; omega) (by decide)
  have sub16 (hp : 0<L s-sl s 0) : (tailArgs s).secondSlot.Sub (dsR s) :=
    Offset.sub_base _ (by have := (rem hp).1; change 16+8 ≤ Cnt s*16; omega)
  have sec (hp : 0<L s-sl s 0) : (tailArgs s).second=sb s 1 := by simp [(rem hp).1]
  refine ⟨e,x0,x1,h1,h2,?_,?_,?_,?_,data,len,?_,lc,le,bounded,?_,?_,?_,?_,?_,?_,
    h.d_w.sub_left dsub,sw.2.2.sub_left ssub,(sw.1.sub_left ssub).sub_right dsub,?_,?_,?_,?_⟩
  · exact fr.readW (r := argR s) (Offset.contains (SP s) (by decide : 8 ≤ 8) (by decide : 8 + 8 ≤ 8 + 48) (by decide)) h.arg_apart (by decide)
  · rw [fr.readW d0 h.desc_apart (by decide)]; simp [sb]
  · rw [fr.readW d8 h.desc_apart (by decide)]; simp [sl]
  · intro hp
    rw [sec hp]
    exact fr.readW (d16 hp) h.desc_apart (by decide)
  · simpa only [tailArgs, ofNat_toNat] using al
  · rw [rd,wr]; exact c.args 0 (by decide)
  · exact Split.covers_pre ds (by change 16 ≤ Cnt s*16; omega)
  · intro hp; exact ds _ _ ⟨_,List.mem_singleton_self _,d16 hp⟩
  · exact Split.covers_off' (sc 0 nz) (by change 16*(sl s 0/16)+sl s 0%16 ≤ sl s 0; omega) (by omega)
  · intro hp
    have ⟨hi, eq⟩ := rem hp
    simp only [TailArgs.secondR,hi,ite_true]
    change Covers [⟨sb s 1,L s-sl s 0⟩] _
    rw [←eq]; exact sc 1 hi
  · rw [wr]; exact Split.covers_off' c.data.wr (by change 16*(sl s 0/16)+(L s-16*(sl s 0/16)) ≤ L s; omega) lc
  · intro hp
    have ⟨hi, eq⟩ := rem hp
    simp only [TailArgs.secondR,hi,ite_true]
    change (⟨sb s 1,L s-sl s 0⟩ : Region).Disjoint _
    rw [←eq]; exact (h.ls _ (slice_mem s hi)).2.2
  · intro hp
    have ⟨hi, eq⟩ := rem hp
    simp only [TailArgs.secondR,hi,ite_true]
    change (⟨sb s 1,L s-sl s 0⟩ : Region).Disjoint _
    rw [←eq]; exact (h.ls _ (slice_mem s hi)).1.sub_right dsub
  · exact fun hp => h.ds_w.sub_left (sub16 hp)
  · exact fun hp => (h.ds_d.sub_left (sub16 hp)).sub_right dsub

theorem whole_frame {u m v : State} (nz : Cnt s ≠ 0) (whole : Layout.WholeDone s u m v) :
    Frame (changed s) s.mem v.mem := by
  obtain ⟨mid, out⟩ := whole
  have lim := (h.front M.ge).le
  have q : sl s 0 ≤ L s := by simpa [fl_eq, nz] using lim
  have w : (⟨W s,2560⟩ : Region) ∈ changed s := List.mem_cons_self ..
  have k : below (SP s) 56 ∈ changed s := by simp [changed]
  have hf := firstMem_frame m.mem (W s) (sb s 0) (Dst s) (L s)
  refine (mid.frame.sub ?_).trans ((hf.sub ?_).trans (out.frame.sub ?_))
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_,w,fun _ a => a⟩
    · exact ⟨_,k,below_sub (by decide) (by decide)⟩
  · intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact ⟨_,w,fun _ a => a⟩
  · intro r hr
    simp only [Split.callWr,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with (rfl | rfl | rfl | rfl) | rfl
    · exact ⟨_,w,fun a x => Split.st_w a (Split.cb_sub a x)⟩
    · exact ⟨_,w,fun a x => Split.st_w a (Split.y_sub a x)⟩
    · exact ⟨dR s,by simp [changed],Region.sub_prefix (by omega)⟩
    · exact ⟨_,w,Split.sc_w⟩
    · exact ⟨_,k,fun _ a => a⟩

theorem whole_slot {u m v : State} (nz : 0 < Cnt s) (whole : Layout.WholeDone s u m v)
    {d : Nat} (lo : 128 ≤ d) (hi : d+8 ≤ 448) :
    v.mem.readW (W s+BitVec.ofNat 64 d) 64 =
      (firstMem m.mem (W s) (sb s 0) (Dst s) (L s)).readW (W s+BitVec.ofNat 64 d) 64 := by
  have c := h.inputs whole.1 nz
  have b := c.sl_le
  exact whole.2.frame.readW (Region.contains_self _ _) (Split.block_slot_disj c.regions (by omega) lo hi) (by decide)

end Layout
namespace Layout
open VG.Spec.Gcm (blockAt)
open VG.Impl.AesGcm.X86_64.Short (finPowP finKsA)
variable {th : Nat} {s : State} (h : Layout (CtxMode.flaggedT th) s)
include h

theorem key_schedule (hf : ShortFacts) (ht : 16 ≤ th) (g : frontGo false s = true) {u m v : State}
    (whole : WholeDone s u m v) :
    WP isa (.seq (.block finPowP) finKsA) v fun t =>
      TailPre (tailArgs s) (ctxH v.mem (K s)) t ∧
      blockAt t.mem (W s+1024#64) = ciphOf v.mem (K s) (s.gpr .rsi).toNat (blockAt v.mem (W s+16#64)) ∧
      blockAt t.mem (W s+1024#64+16#64) = ciphOf v.mem (K s) (s.gpr .rsi).toNat (blockAt v.mem (Split.cbA (W s))) ∧
      Frame [⟨W s+1024#64,64⟩] v.mem t.mem ∧ t.rd=v.rd ∧ t.wr=v.wr := by
  obtain ⟨_, count, _, _⟩ := front_limits (h.front (CtxMode.flaggedT th).ge) g
  have nz : 0<Cnt s := by omega
  have frame := h.whole_frame (Nat.ne_of_gt nz) whole
  have env := whole.2.env
  have rd : v.rd=s.rd := whole.2.rd.trans whole.1.rd
  have wr : v.wr=s.wr := whole.2.wr.trans whole.1.wr
  have ext := h.ext.keep rd wr frame h.ext_apart
  have pp := ext.ok.2.2.1 (Nat.le_trans ht ext.ok.1) 0 (by decide)
  simp only [Nat.mul_zero, Nat.add_zero] at pp
  have cov (o : Nat) (hle : o+16≤1032) : InRegions (v.rd++v.wr) (K s+BitVec.ofNat 64 o) 16 :=
    in_off ext.cov hle (show 1032<2^64 by decide)
  obtain ⟨_,data,len,rs⟩ := firstMem_slots m.mem (W s) (sb s 0) (Dst s) (L s)
  have r := (h.whole_slot nz whole (d := 176) (by decide) (by decide)).trans (rs.trans whole.1.rounds.1)
  have d := (h.whole_slot nz whole (d := 200) (by decide) (by decide)).trans data
  have l := (h.whole_slot nz whole (d := 192) (by decide) (by decide)).trans len
  have a := h.whole_slot nz whole (d := 184) (by decide) (by decide)
  have sep (i : Nat) (hi : 192≤i) (bound : i≤224) :
      Mem.Sep (W s+184#64) (64/8) (W s+BitVec.ofNat 64 i) (64/8) :=
    Offset.sep _ (.inl (by omega)) (by decide) (by omega)
  simp only [firstMem,Mem.readW_writeW_sep (sep 192 (by decide) (by decide)) (by decide),
    Mem.readW_writeW_sep (sep 200 (by decide) (by decide)) (by decide),
    Mem.readW_writeW_sep (sep 224 (by decide) (by decide)) (by decide)] at a
  refine WP.seq (WP.mono (Fast.finPowP_ok hf v env.r13 (cov 272 (by decide)) (cov 256 (by decide)) pp.2 pp.1)
    fun z ⟨x0,x1,h1,h2,o⟩ => ?_)
  have ez := env.keep (fun r hr => o.gpr r (by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> decide)) o.rd o.wr
  refine WP.mono (finKsA_ksOk z ez (o.mem ▸ r) whole.1.rounds.2) fun t ⟨mask,ks,f,regs,tr,tw,x⟩ => ?_
  have et := ez.keep (fun r hr => regs r (by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> decide) (by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> decide) (by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> decide)) tr tw
  rw [o.mem] at mask ks f
  have ft : Frame (changed s) s.mem t.mem := frame.trans (f.sub (fun r hr => by
    simp only [List.mem_singleton] at hr
    subst r
    exact ⟨_,List.mem_cons_self ..,Lay.wSub (by decide)⟩))
  have slot (i : Nat) (hi : i+8≤1024) :
      t.mem.readW (W s+BitVec.ofNat 64 i) 64=v.mem.readW (W s+BitVec.ofNat 64 i) 64 :=
    f.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr
      subst r
      exact Offset.disjoint _ (.inl hi) (by omega) (by decide)) (by decide)
  refine ⟨h.tail_pre g et ft (tr.trans (o.rd.trans rd)) (tw.trans (o.wr.trans wr))
    ((slot 200 (by decide)).trans d) ((slot 192 (by decide)).trans l) ((slot 184 (by decide)).trans (a.trans whole.1.alen))
    ((x _ (by decide) (by decide) (by decide) (by decide)).trans x0)
    ((x _ (by decide) (by decide) (by decide) (by decide)).trans x1) ?_ ?_,mask,ks,f,tr.trans o.rd,tw.trans o.wr⟩
  · rwa [x .xmm3 (by decide) (by decide) (by decide) (by decide)]
  · rwa [x .xmm3 (by decide) (by decide) (by decide) (by decide), x .xmm6 (by decide) (by decide) (by decide) (by decide)]

end Layout
end VG.Proof.AesGcm.X86_64.DirectGather
