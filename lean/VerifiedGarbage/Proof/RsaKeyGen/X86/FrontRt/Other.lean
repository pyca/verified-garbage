module

import VerifiedGarbage.Proof.RsaKeyGen.X86.FrontRt.Close
public import VerifiedGarbage.Proof.RsaKeyGen.X86.FrontRt.Near
public import VerifiedGarbage.Proof.RsaKeyGen.X86.FrontRt.Load
public import VerifiedGarbage.Proof.MillerRabin.X86.WorkspaceFrame
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Proof.RsaKeyGen.X86.FilterStack
import VerifiedGarbage.Proof.RsaKeyGen.X86.WorkspaceDisjoint
import VerifiedGarbage.Proof.RsaKeyGen.FrameOutside
import VerifiedGarbage.Proof.MillerRabin.X86.Caller
import VerifiedGarbage.Proof.Bignum.MemoryFrame
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.RsaKeyGen.X86.FrontRt.Pointer
public import VerifiedGarbage.Spec.RsaKeyGen

/-! # A supplied prime imported into array 4, and its distance to the candidate checked in a frame -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.FrontRt
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86
open VG.Impl.Bignum.X86.PublicContext VG.Impl.RsaKeyGen.X86.FrontRt
open VG.Impl.Mont.X86 (sc at_)

theorem other_ok {W : Addr} {L w : Nat} {s : State} (S : Space W L w s)
    (fit : 40 ≤ (s.gpr .esp).toNat)
    (separateStack : (s.gpr .esp).toNat ≤ W.toNat ∨ W.toNat + L + 40 ≤ (s.gpr .esp).toNat)
    {p : BitVec 32} (pointer : s.mem.readW (off W 20) 32 = p)
    (sourceFit : p.toNat + 8 * w ≤ 2 ^ 32)
    (readable : InRegions (s.rd ++ s.wr) (p.setWidth 64) (8 * w))
    (separate : (⟨p.setWidth 64, 8 * w⟩ : Region).Disjoint ⟨W, L⟩) :
    WP isa other s fun t =>
      t.gpr .eax = Near.bit (Spec.RsaKeyGen.tooClose (64 * w)
        (some (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (p.setWidth 64) (8 * w))))
        (val32 s.mem W (slot w 0) (2 * w))) ∧
      Frame [⟨W, L⟩, below (s.gpr .esp) 20] s.mem t.mem ∧
      WorkspaceFrame ⟨W, L, w⟩ [(slot w 4, 8 * w), (slot w 2, 8 * w), (slot w 3, 8 * w)] s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  have nowrap := S.scratch.nowrap
  have head := S.header
  have ⟨f0, l0, _⟩ := arrays0.fit S
  have ⟨f2, l2, _⟩ := arrays2.fit S
  have ⟨f3, l3, _⟩ := arrays3.fit S
  have ⟨f4, l4, _⟩ := arrays4.fit S
  have a04 := Arrays.apart arrays0 arrays4 (w := w) (by decide)
  unfold other
  refine WP.seq (wp_movS (readSrc_sc S.scratch (d := 20) (by omega)) fun a A _ => WP.block_nil ?_)
  have Sa := S.keepMem A.keeps (by decide) (by decide) A.mem
  refine WP.seq (WP.mono (importAt_ok Sa 4 (by decide) f4 (A.gpr.trans pointer)
      sourceFit (by rw [A.keeps.2.1, A.keeps.2.2]; exact readable) separate) fun b ⟨value, Fb, Kb⟩ => ?_)
  rw [A.mem] at value Fb
  have Ob : Outside W (slot w 4) (8 * w) s.mem b.mem := VG.Proof.RsaKeyGen.frame_outside Fb (by omega)
  have lenB : b.mem.readW (off W 4) 32 = a.mem.readW (off W 4) 32 := by
    rw [A.mem]; exact BitVec.eq_of_toNat_eq (Ob.w32 (d := 4) (Or.inl (by omega)) (by omega))
  have Sb := Sa.keep Kb (by decide) (by decide) lenB
  have Kab : Keeps [.eax, .ebx, .esi, .ecx, .edx] s b := (A.keeps.mono (by decide)).trans Kb
  have spB : b.gpr .esp = s.gpr .esp := Kab.1 .esp (by decide)
  refine WP.frameAlloc (by decide) (by decide) (by decide) (by rw [spB]; omega) (NoSp.of_all (by rfl)) ?_
  have St := FilterStack.allocated_context (s := b) (by rw [spB]; omega)
  have apartQ : (⟨W, L⟩ : Region).Disjoint ⟨(b.gpr .esp - 20#32).setWidth 64, 20⟩ :=
    FilterStack.allocated_apart (by rw [spB]; omega) nowrap (by rw [spB]; rcases separateStack with h | h; exact Or.inl h; exact Or.inr (by omega))
  have Sc : Space W L w (allocFrame 20 b) :=
    ⟨FilterStack.allocated_scratch Sb.scratch (by rw [spB]; omega) (by rw [spB]; rcases separateStack with h | h; exact Or.inl h; exact Or.inr (by omega)),
      Sb.width, Sb.widthBound, Sb.space, Sb.len⟩
  have ediB : b.gpr .edi = BitVec.ofNat 32 W.toNat := by
    apply BitVec.eq_of_toNat_eq
    rw [Sb.edi_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine WP.seq (WP.mono (St.store 0 (by decide) .edi) fun c ⟨Mc, Oc, Kc, Stc⟩ => ?_)
  have Fc := VG.Proof.Bignum.outside_frame Oc (by decide)
  have Wc : WorkspaceFrame ⟨W, L, w⟩ [] b.mem c.mem := by
    have H := VG.Proof.RsaKeyGen.X86.workspace_of_frame (g := ⟨W, L, w⟩) Fc nowrap (by
      intro r mem
      obtain rfl := List.mem_singleton.mp mem
      exact apartQ.sub_right (Offset.sub_base _ (by decide)))
    exact H
  have Fcx : Framed W L w (b.gpr .esp - 20#32) c := by
    refine ⟨Sc.keep Kc (by decide) (by decide) (Wc.read32 (d := 4) (by change 4 + 4 ≤ L; omega) (fun _ mem => nomatch mem)),
      Stc, apartQ, ?_⟩
    rw [Mc, Mem.readW_writeW_self32, allocFrame_gpr _ _ (by decide), ediB]
  refine WP.seq (WP.mono (difference_ok Fcx) fun d ⟨D, Od, Kd, Fd⟩ => ?_)
  refine WP.mono (near_ok Fd.space) fun t ⟨result, Mt, Kt⟩ => ?_
  rw [show 4 * (2 * w) = 8 * w by omega] at Od
  have cand : val32 c.mem W (slot w 0) (2 * w) = val32 s.mem W (slot w 0) (2 * w) := by
    rw [Wc.val32 (d := slot w 0) (n := 2 * w) (by change _ ≤ L; omega) (fun _ mem => nomatch mem)]
    exact Ob.val32 (by rcases a04 with h | h; exact Or.inl h; exact Or.inr (by omega)) (by omega)
  have prime : val32 c.mem W (slot w 4) (2 * w) = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (p.setWidth 64) (8 * w)) := by
    rw [Wc.val32 (d := slot w 4) (n := 2 * w) (by change _ ≤ L; omega) (fun _ mem => nomatch mem)]
    exact value
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [freed_gpr _ _ (by decide), result, D, cand, prime, show 32 * (2 * w) = 64 * w by omega]
    rfl
  · rw [freed_mem, Mt]
    have F1 : Frame [⟨W, L⟩, below (s.gpr .esp) 20] s.mem b.mem :=
      Fb.sub fun r mem => by
        obtain rfl := List.mem_singleton.mp mem
        exact ⟨_, List.mem_cons_self, Offset.sub_base W f4⟩
    have F2 : Frame [⟨W, L⟩, below (s.gpr .esp) 20] b.mem c.mem := by
      change Frame _ b.mem c.mem at Fc
      refine Fc.sub fun r mem => ?_
      obtain rfl := List.mem_singleton.mp mem
      refine ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩
      rw [spB]
      exact Offset.sub_base _ (by decide)
    have F3 : Frame [⟨W, L⟩, below (s.gpr .esp) 20] c.mem d.mem :=
      (workspaceGlobalFrame (g := ⟨W, L, w⟩) Od (by
        intro r mem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
        rcases mem with rfl | rfl
        · exact f2
        · exact f3)).mono fun r mem => by
          obtain rfl := List.mem_singleton.mp mem
          exact List.mem_cons_self
    exact (F1.trans F2).trans F3
  · rw [freed_mem, Mt]
    have W1 : WorkspaceFrame ⟨W, L, w⟩ [(slot w 4, 8 * w), (slot w 2, 8 * w), (slot w 3, 8 * w)] s.mem b.mem :=
      WorkspaceFrame.of_outs nowrap (Outs.of_outside Ob List.mem_cons_self)
    have W2 : WorkspaceFrame ⟨W, L, w⟩ [(slot w 4, 8 * w), (slot w 2, 8 * w), (slot w 3, 8 * w)] b.mem c.mem := by
      exact Wc.mono fun _ mem => nomatch mem
    have W3 : WorkspaceFrame ⟨W, L, w⟩ [(slot w 4, 8 * w), (slot w 2, 8 * w), (slot w 3, 8 * w)] c.mem d.mem :=
      (WorkspaceFrame.of_outs (g := ⟨W, L, w⟩) nowrap Od).mono fun r mem => List.mem_cons_of_mem _ mem
    exact (W1.trans W2).trans W3
  · have Kin : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] (allocFrame 20 b) t :=
      ((Kc.mono (by decide)).trans Kd).trans (Kt.mono (by decide))
    exact (Kab.mono (by decide)).trans (FilterStack.freed_keeps Kin (by decide))

theorem close_ok {W : Addr} {L w : Nat} {s : State} (S : Space W L w s)
    (fit : 40 ≤ (s.gpr .esp).toNat)
    (separateStack : (s.gpr .esp).toNat ≤ W.toNat ∨ W.toNat + L + 40 ≤ (s.gpr .esp).toNat)
    {p plen : BitVec 32} (pointer : s.mem.readW (off W 20) 32 = p)
    (lengthEq : s.mem.readW (off W 24) 32 = plen)
    (source : plen ≠ 0#32 → p.toNat + 8 * w ≤ 2 ^ 32 ∧
      InRegions (s.rd ++ s.wr) (p.setWidth 64) (8 * w) ∧
      (⟨p.setWidth 64, 8 * w⟩ : Region).Disjoint ⟨W, L⟩) :
    WP isa close s fun t =>
      t.gpr .eax = Near.bit (Spec.RsaKeyGen.tooClose (64 * w)
        (if plen = 0#32 then none else some (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (p.setWidth 64) (8 * w))))
        (val32 s.mem W (slot w 0) (2 * w))) ∧
      Frame [⟨W, L⟩, below (s.gpr .esp) 20] s.mem t.mem ∧
      WorkspaceFrame ⟨W, L, w⟩ [(slot w 4, 8 * w), (slot w 2, 8 * w), (slot w 3, 8 * w)] s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  have head := S.header
  unfold close
  refine WP.seq (wp_movS (readSrc_sc S.scratch (d := 24) (by omega)) fun a A _ =>
    wp_cmpS rfl fun b B Z => WP.block_nil ?_)
  have K : Keeps [.eax] s b := A.keeps.widen (B.keeps [])
  have M : b.mem = s.mem := B.mem.trans A.mem
  have condition : isa.eval .e b = some (decide (plen = 0#32)) := by
    change b.zf = _
    rw [Z, A.gpr, lengthEq]
    change some (plen - 0#32 == 0#32) = _
    rw [BitVec.sub_zero]
    rfl
  have spB : b.gpr .esp = s.gpr .esp := K.1 .esp (by decide)
  by_cases absent : plen = 0#32
  · refine WP.ite true (by rw [condition, decide_eq_true absent]) (fun _ => ?_) (fun impossible => nomatch impossible)
    refine wp_movS rfl fun t T _ => WP.block_nil ?_
    have Mt : t.mem = s.mem := T.mem.trans M
    refine ⟨?_, by rw [Mt]; exact Frame.refl _ _, by rw [Mt]; exact WorkspaceFrame.refl _ _ _,
      (K.mono (by decide)).widen T.keeps⟩
    rw [T.gpr]
    simp only [absent, ↓reduceIte, Spec.RsaKeyGen.tooClose, Near.bit, Bool.toNat_false]
    rfl
  · refine WP.ite false (by rw [condition, decide_eq_false absent]) (fun impossible => nomatch impossible) (fun _ => ?_)
    obtain ⟨sourceFit, readable, separate⟩ := source absent
    refine WP.mono (other_ok (S.keepMem K (by decide) (by decide) M) (by rw [spB]; exact fit)
      (by rw [spB]; exact separateStack) (by rw [M]; exact pointer) sourceFit
      (by rw [K.2.1, K.2.2]; exact readable) separate) fun t ⟨result, F, Wt, Kt⟩ => ?_
    rw [M] at result F Wt
    rw [spB] at F
    exact ⟨by simpa only [absent, ↓reduceIte] using result, F, Wt, (K.mono (by decide)).trans Kt⟩

/-- A supplied prime's source, at header byte 20. -/
structure OtherIn (W : Addr) (L w : Nat) (q p : BitVec 32) (s : State) : Prop where
  base : Base W L w q s
  pointer : s.mem.readW (off W 20) 32 = p
  sourceFit : p.toNat + 8 * w ≤ 2 ^ 32
  readable : InRegions (s.rd ++ s.wr) (p.setWidth 64) (8 * w)
  separate : (⟨p.setWidth 64, 8 * w⟩ : Region).Disjoint ⟨W, L⟩

/-- The distance check's inputs: `p` at header byte 20 and its length at 24. -/
structure CloseIn (W : Addr) (L w : Nat) (q p plen : BitVec 32) (s : State) : Prop where
  base : Base W L w q s
  pointer : s.mem.readW (off W 20) 32 = p
  length : s.mem.readW (off W 24) 32 = plen
  source : plen ≠ 0#32 → p.toNat + 8 * w ≤ 2 ^ 32 ∧
    InRegions (s.rd ++ s.wr) (p.setWidth 64) (8 * w) ∧ (⟨p.setWidth 64, 8 * w⟩ : Region).Disjoint ⟨W, L⟩

end VG.Proof.RsaKeyGen.X86.FrontRt
