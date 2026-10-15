module

public import VerifiedGarbage.Proof.X25519.AArch64.Hybrid.VSave
public import VerifiedGarbage.Proof.Ed25519.AArch64.Divstep
public import VerifiedGarbage.Proof.X25519.AArch64.Word.Top
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.X25519.AArch64.Hybrid.Lit
import VerifiedGarbage.Proof.Ed25519.AArch64.MulAddMemory
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# X25519 on AArch64: the hybrid ladder's whole function

Untrusted: everything here is checked by Lean. The four-word function's setup,
then `v8`–`v15` saved and the products' constants written; the hybrid ladder;
the four-word function's last swap, inversion and output, with `v8`–`v15`
restored first.
-/

@[expose] public section

namespace VG.Proof.X25519.AArch64.Hybrid

open VG VG.AArch64 VG.Spec.X25519 VG.Proof.X25519
open VG.Impl.Ed25519.AArch64 (Slot offset)
open VG.Impl.X25519.AArch64.Hybrid (VSAVE)
open VG.Impl.X25519.AArch64.Neon (V CONST)
open VG.Proof.Ed25519.AArch64 (env F Outside ofs clob word off ofs_off' Saved)
open VG.Proof.X25519.AArch64.Word (LoopKeep Good bitOffset localContract Kp Sc saved_of_words preservedCases)

theorem HLoopKeep.kp {base : Addr} {s t : State} (h : HLoopKeep base s t) :
    Kp (clob ++ ([.x19] : List Reg)) s t :=
  ⟨fun r hr => h.gpr r (fun hc => hr (List.mem_append_left _ hc))
    (fun hc => hr (List.mem_append_right _ (by simp [hc]))), h.rd, h.wr⟩

theorem env_of_high {base : Addr} {m m' : Mem} (h : Outside base 1104 176 m m') : env m' base = env m base := by
  funext i
  simp only [env, F]
  rw [VG.Proof.Ed25519.AArch64.Outside.fe h (by simp only [offset]; omega) (by simp only [offset]; omega)]

theorem preservedV_cases : ∀ r ∈ preservedV, ∃ k < 8, r = V (8 + k) := by decide

theorem preservedV_of : ∀ k < 8, V (8 + k) ∈ preservedV := by decide

theorem hsetup_ok {base sc pt : Addr} {s : State} (hs : Sc base s)
    (hn : base.toNat+4096 ≤ 2^64) (h1 : s.gpr .x1 = sc) (h2 : s.gpr .x2 = pt)
    (hsr : (⟨sc,32⟩ : Region) ∈ s.rd) (hpr : (⟨pt,32⟩ : Region) ∈ s.rd)
    (hdS : (⟨sc,32⟩ : Region).Disjoint ⟨base,4096⟩)
    (hdP : (⟨pt,32⟩ : Region).Disjoint ⟨base,4096⟩) :
    WP isa (.block VG.Impl.X25519.AArch64.Hybrid.setup) s fun t =>
      Scratch t base ∧ Good (env t.mem base) (toFe (decodeUCoordinate (bytesAt s.mem pt 32)))
        (init (toFe (decodeUCoordinate (bytesAt s.mem pt 32)))) ∧
      word t.mem base 768 = 0 ∧ t.gpr .x1 = s.gpr .x0 ∧
      (∀ i < 255, t.mem (off base (bitOffset+i)) = BitVec.ofNat 8 (bit (decodeScalar25519 (bytesAt s.mem sc 32)) i)) ∧
      (∀ i < 6, word t.mem base (8*i) = s.gpr (VG.Impl.X25519.AArch64.saved.getD i .x19)) ∧
      Kp (clob ++ ([.x0,.x1,.x19] : List Reg)) s t ∧ Consts t.mem base ∧ SavedV base s.v t.mem := by
  have hV : VSAVE = 1152 := rfl
  have hC : CONST = 1104 := rfl
  rw [VG.Impl.X25519.AArch64.Hybrid.setup, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (WP.preservedV (VG.Proof.X25519.AArch64.Word.setup_ok hs hn h1 h2 hsr hpr hdS hdP) (by lit_decide))
    fun a ⟨⟨ha, ga, wa, oa, ba, sva, ka⟩, va⟩ => ?_
  refine WP.mono (vsave_ok ha) fun b ⟨svb, ob, gb, vb, rb, wb, spb⟩ => ?_
  have hb : Scratch b base := scratch_of ha gb wb
  refine WP.mono (consts_ok hb) fun c ⟨cc, oc, gc, vc, rc, wc, spc⟩ => ?_
  have o : Outside base 1104 176 a.mem c.mem :=
    VG.Proof.Ed25519.AArch64.Outside.trans (VG.Proof.Ed25519.AArch64.Outside.mono ob (by omega) (by omega))
      (VG.Proof.Ed25519.AArch64.Outside.mono oc (by omega) (by omega))
  have g2 : ∀ r, r ≠ .x2 → c.gpr r = a.gpr r := fun r hr => by rw [gc r hr, gb]
  refine ⟨⟨(g2 _ (by decide)).trans ha.x0, wc ▸ wb ▸ ha.wr, ha.nowrap⟩, by rw [env_of_high o]; exact ga,
    by rw [Outside.word' o (by omega) (by omega)]; exact wa, by rw [g2 _ (by decide)]; exact oa,
    fun i hi => ?_, fun i hi => by rw [Outside.word' o (by omega) (by omega)]; exact sva i hi,
    ⟨fun r hr => ?_, rc.trans (rb.trans ka.rd), wc.trans (wb.trans ka.wr)⟩, cc,
    fun k hk => ((svb.outside oc (by omega)) k hk).trans (va _ (preservedV_of k hk))⟩
  · rw [o]
    · exact ba i hi
    · rw [ofs_off' base (by simp [bitOffset, VG.Impl.X25519.AArch64.Word.BITS, VG.Impl.X25519.AArch64.BITS,
        VG.Impl.X25519.AArch64.slot, VG.Impl.X25519.AArch64.NSLOT]; omega)]
      right
      simp [bitOffset, VG.Impl.X25519.AArch64.Word.BITS, VG.Impl.X25519.AArch64.BITS,
        VG.Impl.X25519.AArch64.slot, VG.Impl.X25519.AArch64.NSLOT]
      omega
  · rw [g2 r (fun e => hr (e ▸ by decide))]
    exact ka.gpr r hr

theorem correct {s₀ : State} (hp : localContract.pre s₀) :
    WP isa VG.Impl.X25519.AArch64.Hybrid.x25519 s₀ fun t =>
      (∀ r ∈ preserved, t.gpr r = s₀.gpr r) ∧
      (∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (s₀.v r).extractLsb' 0 64) ∧ localContract.post s₀ t := by
  have pre := VG.Proof.X25519.AArch64.Pre.of s₀ hp.1
  let base := s₀.gpr .x3
  have hs : Sc base s₀ := ⟨rfl,by rw [pre.wr]; simp [base,VG.Proof.X25519.AArch64.scR]⟩
  have hV : VSAVE = 1152 := rfl
  rw [VG.Impl.X25519.AArch64.Hybrid.x25519]
  refine WP.seq (WP.mono (hsetup_ok hs hp.2 rfl rfl
    (by rw [pre.rd]; simp) (by rw [pre.rd]; simp) pre.scalar_sc pre.point_sc)
    fun c ⟨hc, gc, wc, oc, bc, svc, kc, cc, svv⟩ => ?_)
  refine WP.seq (WP.mono (ladder_ok hc cc gc wc bc) fun d ⟨kd, gd, wd⟩ => ?_)
  have hd := kd.scratch hc
  refine WP.seq (WP.mono (VG.Proof.X25519.AArch64.Word.lastSwap_ok hd gd (ladderAfter_swap_le _ _ (by decide)) wd)
    fun e ⟨ke, ex, ez⟩ => ?_)
  have he := ke.scratch hd
  refine WP.seq (WP.mono (VG.Proof.Ed25519.AArch64.Divstep.invert_ok he) fun f ⟨fi, fk, f1, fm⟩ => ?_)
  have hf : Scratch f base := ⟨(fk.gpr _ (by decide)).trans he.x0, fk.wr ▸ he.wr, he.nowrap⟩
  have svf : SavedV base s₀.v f.mem :=
    ((svv.outside kd.mem (by omega)).outside ke.mem (by omega)).outside fm (by omega)
  have saved : Saved base s₀.gpr f.mem :=
    (((saved_of_words svc).outside kd.mem (by decide)).outside ke.mem (by decide)).outside fm (by decide)
  have out : f.gpr .x1 = s₀.gpr .x0 :=
    f1.trans ((ke.gpr _ (by decide) (by decide)).trans ((kd.gpr _ (by decide) (by decide)).trans oc))
  have dx : env f.mem base 1 = env e.mem base 1 :=
    congrArg toFe (VG.Proof.Ed25519.AArch64.Outside.fe fm (Or.inl (by decide : offset 1+32 ≤ 192))
      (by decide))
  have kf' : Kp (.x19 :: VG.Proof.Mont.AArch64.clob 4 ++ [.x2, .x20]) e f := ⟨fk.gpr, fk.rd, fk.wr⟩
  rw [VG.Impl.X25519.AArch64.Hybrid.finish, WP.block_append_iff]
  refine WP.mono (vrestore_ok hf svf) fun g ⟨gv, gm, gg, gr, gw, gsp⟩ => ?_
  have hg : Scratch g base := scratch_of hf gg gw
  refine WP.mono (WP.preservedV (VG.Proof.X25519.AArch64.Word.finish_ok (g := s₀.gpr) hg (by rw [gg]; exact out)
    (by rw [gw, fk.wr, ke.wr, kd.wr, kc.wr, pre.wr]; simp) pre.out_sc (by rw [gm]; exact saved)) (by lit_decide))
    fun t ⟨⟨tg, kt, rt⟩, tv⟩ => ?_
  refine ⟨fun r hr => ?_, fun r hr => ?_, ?_⟩
  · rcases preservedCases r hr with ⟨rd,hrd,er⟩ | hn
    · rw [← er]; exact tg rd hrd
    · have kfg : Kp ([] : List Reg) f g := ⟨fun r _ => by rw [gg], gr, gw⟩
      have kk := ((((kc.trans kd.kp).trans ke.kp).trans kf').trans kfg).trans kt
      exact kk.sub (by decide) |>.gpr r hn
  · obtain ⟨k, hk, rfl⟩ := preservedV_cases r hr
    rw [tv _ hr, gv k hk]
  · change bytesAt t.mem (s₀.gpr .x0) 32 = Spec.X25519.x25519
      (bytesAt s₀.mem (s₀.gpr .x1) 32) (bytesAt s₀.mem (s₀.gpr .x2) 32)
    rw [rt, gm, dx, fi, ex, ez, x25519_eq]

theorem x25519_ok (s : State) (hs : localContract.pre s) :
    ∃ tr t, Exec isa VG.Impl.X25519.AArch64.Hybrid.x25519 s tr t ∧ abiPreserved s t ∧ localContract.post s t := by
  obtain ⟨tr,t,he,hg,hv,hp⟩ := correct hs
  exact ⟨tr,t,he,⟨hg,Exec.sp he,hv⟩,hp⟩

end VG.Proof.X25519.AArch64.Hybrid
