module

public import VerifiedGarbage.Proof.AesGcm.X86_64.OpenSplit.Prefix
import VerifiedGarbage.Proof.AesGcm.X86_64.CTBase
import VerifiedGarbage.Proof.AesGcm.X86_64.Cmp
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Framework.X86_64.Taint
meta import VerifiedGarbage.Proof.AesGcm.X86_64.BlocksTo.Verified
meta import VerifiedGarbage.TCB.X86_64.Isa
meta import VerifiedGarbage.Impl.AesGcm.X86_64.BlocksToDec
import VerifiedGarbage.Proof.AesGcm.X86_64.OneBlocks.Call

/-! Correctness of the internal one-stack-argument AES-GCM seal entry. -/

@[expose] public section

namespace VG.Proof.AesGcm.X86_64.BlocksToDec

open VG VG.X86_64 VG.Impl.AesGcm.X86_64 VG.Proof.AesGcm.X86_64.BlocksTo
open VG.Proof.Gcm.X86_64.Stitch (CtxMode SPreTo EPostTo)

private theorem sameInput {s t : State} (g : t.gpr = s.gpr) (m : t.mem = s.mem)
    (rd : t.rd = s.rd) (wr : t.wr = s.wr) {M : CtxMode} (hp : BT M s true true) :
    BT M t true true ∧ (∀ u, Done t u true → Done s u true) := by
  cases s; cases t; cases g; cases m; cases rd; cases wr
  exact ⟨{ hp with }, fun _ h => h⟩

private theorem entryMid {s : State} {M : CtxMode} (hp : BT M s true true) :
    WP isa (.block (Impl.AesGcm.X86_64.BlocksTo.entry true)) s (fun t => Mid s 0 0 t true) :=
  WP.mono (entry_ok hp) fun t ⟨_, _, regs, kept, frame, rd, wr⟩ =>
    BlocksTo.mid_entry hp (regs _ (by decide) (by decide)) (fun r hr => by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact regs _ (by decide) (by decide))
      kept frame rd wr

theorem sealPrepared_wp {s : State} {M : CtxMode} (hp : BT M s true true)
    {aligned : Bool} {piece : Prog isa} {minimum : Nat}
    (cut : (minimum = 2 ∨ minimum = 5) ∨ minimum = 16)
    (ok : ∀ t, SPreTo M t minimum → WP isa piece t (EPostTo t))
    (g : GhashImpl) (v : Proof.Aes.X86_64.Ctr32ToImpl) :
    WP isa (Impl.AesGcm.X86_64.BlocksToDec.sealPrepared ⟨v.callee.name, v.callee.code⟩
      g.fn piece aligned minimum) s (fun u => Done s u true) := by
  refine WP.seq (WP.mono (cmpMinimum_ok cut (s := s) rfl) fun t ⟨regs, mem, rd, wr, flag⟩ => ?_)
  obtain ⟨pre, post⟩ := sameInput regs mem rd wr hp
  refine WP.ite (decide (n s < minimumFor minimum (n s))) (by simp only [eval, flag]) (fun _ => ?_) (fun he => ?_)
  · apply WP.mono _ post
    refine WP.seq (WP.mono (entryMid pre) fun u h => ?_)
    refine WP.seq (WP.mono (BlocksTo.tailHead_ok pre h) fun u ⟨mid, z, _⟩ => ?_)
    refine WP.ite (decide (n t - 0 = 0)) (by simp only [eval, z]) (fun e => ?_) (fun _ => ?_)
    · exact WP.block_nil (BlocksTo.done_of pre mid (by simpa using e))
    · exact WP.seq (WP.mono (encryptCtr_ok pre v mid) fun _ h => encryptHash_ok pre g h)
  · have hn : minimumFor minimum (n s) ≤ n s := by simpa using he
    have hmin : minimum ≤ minimumFor minimum (n s) := by
      by_cases h : minimum = 5
      · rw [h]; unfold minimumFor; simp only [↓reduceIte]; split <;> decide
      · simp [minimumFor,h]
    apply WP.mono _ post
    apply fusedWhole_ok pre _ ok
    simpa only [n, regs] using (Nat.le_trans hmin hn)

/-- Public registers entering the fused program after scratch is loaded. -/
def sealRegs : List Reg := [.r10, .r11, .rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp]

private abbrev Pair (M : CtxMode) (a b : State) := BT M a true true ∧ BT M b true true ∧ Pub a b true

private theorem scratchPublic {M : CtxMode} {a b : State} (h : Pair M a b) :
    a.mem.readW (a.gpr .rsp + BitVec.ofNat 64 8) 64 = b.mem.readW (b.gpr .rsp + BitVec.ofNat 64 8) 64 ∧
    InRegions (a.rd ++ a.wr) (a.gpr .rsp + BitVec.ofNat 64 8) 8 ∧
    InRegions (b.rd ++ b.wr) (b.gpr .rsp + BitVec.ofNat 64 8) 8 :=
  ⟨h.2.2.sc.symm, a_in h.1 (i := 0) (by decide), a_in h.2.1 (i := 0) (by decide)⟩

private theorem shortRel {M : CtxMode} (g : GhashImpl) (v : Proof.Aes.X86_64.Ctr32ToImpl) :
    RelCT isa (Pair M) (.seq (.block (Impl.AesGcm.X86_64.BlocksTo.entry true))
      (Impl.AesGcm.X86_64.BlocksToDec.encryptShort ⟨v.callee.name, v.callee.code⟩ g.fn true)) fun _ _ => True := by
  intro a b t u x y h ea eb
  let en := Impl.AesGcm.X86_64.BlocksTo.entry true
  have start := (rel_r11At true (l₀ := en) (l := en.tail) (P := fun p q => p = a ∧ q = b)
    rfl [.rsp] [] (by simp) (fun _ _ ⟨rfl,rfl⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.2.2.sp.symm)
    (fun _ _ ⟨rfl,rfl⟩ => scratchPublic h) (by dsimp only [en]; exact ⟨_, by taint_decide⟩)).wp
    (F₁ := fun t => Mid a 0 0 t true) (F₂ := fun t => Mid b 0 0 t true) (fun p q eqs => by obtain ⟨rfl,rfl⟩ := eqs; exact ⟨entryMid h.1, entryMid h.2.1⟩)
  let head : List Instr := [.mov .r11 (.mem (at_ .rsp 8)), .mov .rcx (.mem (at_ .r11 Blocks.argN)), .alu .test .rcx (.reg .rcx)]
  have check := (rel_r11At true (l₀ := head) (l := head.tail) rfl [.rsp] [] (by simp)
    (P := fun p q => Mid a 0 0 p true ∧ Mid b 0 0 q true)
    (fun _ _ h' => BlocksTo.mid_rsp h.2.2 h'.1 h'.2) (fun _ _ h' => BlocksTo.mid_hS h.1 h.2.1 h.2.2 h'.1 h'.2)
    (by dsimp only [head]; exact ⟨_, by taint_decide⟩)).wp
    (F₁ := fun t : State => Mid a 0 0 t true ∧ t.zf = some (decide (n a = 0)))
    (F₂ := fun t : State => Mid b 0 0 t true ∧ t.zf = some (decide (n b = 0)))
    (fun _ _ m => ⟨WP.mono (BlocksTo.tailHead_ok h.1 m.1) (fun _ k => ⟨k.1,k.2.1⟩),
      WP.mono (BlocksTo.tailHead_ok h.2.1 m.2) (fun _ k => ⟨k.1,k.2.1⟩)⟩)
  apply RelCT.seq start (RelCT.seq (check.mono (fun _ _ x => x.2) (fun _ _ x => x))
    (rel_ite_e (fun _ _ x => by rw [x.2.1.2, x.2.2.2, h.2.2.en]) ?_ ?_)) _ _ _ _ _ _ ⟨rfl,rfl⟩ ea eb
  · exact (rel_taint [] (fun _ _ _ r hr => by cases hr) empty_check).mono (fun _ _ x => x) (fun _ _ x => x)
  · exact (encryptCalls_rel h.1 h.2.1 h.2.2 g v).mono (fun _ _ x => ⟨x.1.2.1.1, x.1.2.2.1⟩) (fun _ _ x => x)

private theorem pair_congr {M : CtxMode} {a b a' b' : State} (h : Pair M a b)
    (ag : a'.gpr = a.gpr) (am : a'.mem = a.mem) (ar : a'.rd = a.rd) (aw : a'.wr = a.wr)
    (bg : b'.gpr = b.gpr) (bm : b'.mem = b.mem) (br : b'.rd = b.rd) (bw : b'.wr = b.wr) : Pair M a' b' := by
  cases a; cases b; cases a'; cases b'; cases ag; cases am; cases ar; cases aw; cases bg; cases bm; cases br; cases bw
  exact ⟨{ h.1 with }, { h.2.1 with }, { h.2.2 with }⟩

theorem sealPrepared_ct {M : CtxMode} {aligned : Bool} {piece : Prog isa} {minimum : Nat}
    (cut : (minimum = 2 ∨ minimum = 5) ∨ minimum = 16)
    (ct : ∃ hc, (taint.check (Taint.ofRegs sealRegs) piece hc).isSome = true)
    (g : GhashImpl) (v : Proof.Aes.X86_64.Ctr32ToImpl) :
    ConstantTime isa (fun s => BT M s true true) (fun a b => Pub a b true)
      (Impl.AesGcm.X86_64.BlocksToDec.sealPrepared ⟨v.callee.name,v.callee.code⟩ g.fn piece aligned minimum) := by
  apply RelCT.constantTime
  let regs : List Reg := [.r10, .rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp]
  have agree : ∀ a b, Pair M a b → ∀ r ∈ regs, a.gpr r = b.gpr r := by
    intro a b h r hr
    simp only [regs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [h.2.2.dst.symm, h.2.2.k.symm, h.2.2.rsi.symm, h.2.2.c.symm, h.2.2.y.symm,
      h.2.2.src.symm, h.2.2.r9.symm, h.2.2.sp.symm]
  let ptrs := Impl.AesGcm.X86_64.BlocksTo.pointers true ++ Blocks.scratchSetup aligned
  have setup := rel_r11At true (l₀ := ptrs) (l := Blocks.scratchSetup aligned) rfl regs sealRegs
    (by simp [regs]) agree (fun _ _ h => scratchPublic h) (by dsimp only [regs]; cases aligned <;> exact ⟨_, by taint_decide⟩)
  have fused := RelCT.seq setup (rel_taint sealRegs (fun _ _ h => h) ct)
  have cmp := (rel_taint (P := Pair M) [.r9] (fun _ _ h r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact h.2.2.r9.symm)
    (c := Impl.AesGcm.X86_64.BlocksTo.compareCount minimum)
    (by rcases cut with (rfl | rfl) | rfl <;> exact ⟨_, by taint_decide⟩)).wpDep
    (F := fun (a t : State) => t.gpr = a.gpr ∧ t.mem = a.mem ∧ t.rd = a.rd ∧ t.wr = a.wr ∧
      t.cf = some (decide (n a < minimumFor minimum (n a))))
    (fun a b _ => ⟨cmpMinimum_ok cut (s := a) rfl, cmpMinimum_ok cut (s := b) rfl⟩)
  have guard := cmp.mono (fun _ _ h => h) (fun a b h => by
    obtain ⟨_, x, y, h, ⟨ag, am, ar, aw, af⟩, bg, bm, br, bw, bf⟩ := h
    exact (show Pair M a b ∧ a.cf = b.cf from
      ⟨pair_congr h ag am ar aw bg bm br bw, by rw [af, bf, h.2.2.en]⟩))
  exact RelCT.seq guard (RelCT.ite (fun _ _ h => h.2)
    ((shortRel g v).mono (fun _ _ h => h.1.1) (fun _ _ h => h))
    (fused.mono (fun _ _ h => h.1.1) (fun _ _ h => h)))

end VG.Proof.AesGcm.X86_64.BlocksToDec

namespace VG.Proof.AesGcm.X86_64.BlocksTo

open VG VG.X86_64 VG.Impl.AesGcm.X86_64
open VG.Proof.Gcm.X86_64.Stitch (CtxMode SPreTo EPostTo)

/-- The internal two-pointer function used by both public seal layouts. -/
structure SealFn (M : CtxMode) where
  fn : Fn
  wp : ∀ s, BT M s true true → WP isa fn.code s (fun t => Done s t true)
  ct : ConstantTime isa (fun s => BT M s true true) (fun a b => Pub a b true) fn.code
  noSp : NoSp fn.code
  depth : fn.code.depth = 1
  xd : fn.code.x86_64Depth ≤ 8
  mx : fn.code.allInstrs (fun i => !loadsMxcsr i) = true
  spAll : fn.code.all (fun i => !isa.writesSp i) = true

def SealFn.ofFull {M : CtxMode} {piece : Prog isa} (name : String)
    (g : GhashImpl) (v : Proof.Aes.X86_64.Ctr32ToImpl) {minimum : Nat}
    (cut : (minimum = 2 ∨ minimum = 5) ∨ minimum = 16)
    (ok : ∀ t, SPreTo M t minimum → WP isa piece t (EPostTo t))
    (pc : PieceTo piece true true minimum)
    (ct : ∃ hc, (taint.check (Taint.ofRegs BlocksToDec.sealRegs) piece hc).isSome = true) : SealFn M := by
  let code := Impl.AesGcm.X86_64.BlocksToDec.sealPrepared ⟨v.callee.name,v.callee.code⟩ g.fn piece true minimum
  have nc : v.callee.code.allInstrs (fun i => !Taint.clobbers i .rsp) = true := by
    rw [Code.allInstrs_eq, List.all_eq_true]; intro i hi; simp [v.nosp i hi]
  refine ⟨⟨name,code⟩, fun _ h => BlocksToDec.sealPrepared_wp h cut ok g v, BlocksToDec.sealPrepared_ct cut ct g v,
    nosp_of_all ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    simp only [code, Impl.AesGcm.X86_64.BlocksToDec.sealPrepared, Impl.AesGcm.X86_64.BlocksToDec.encryptShort,
      Code.allInstrs, Code.all, Code.depth, Code.x86_64Depth, v.depth, g.depth, pc.depth, pc.nosp, nc,
      gh_nosp_all g, v.spSafe, g.spSafe, pc.spSafe, v.mxcsr, g.mxcsr, pc.mxcsr, v.noStack, g.noStack, pc.xdepth]
    rcases cut with (rfl | rfl) | rfl <;> decide +kernel

end VG.Proof.AesGcm.X86_64.BlocksTo
