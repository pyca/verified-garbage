module
public import VerifiedGarbage.Impl.AesGcm.X86_64.Contiguous
public import VerifiedGarbage.Proof.AesGcm.X86_64.DirectGather.Call
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Gcm.Stream
import VerifiedGarbage.Proof.AesGcm.X86_64.Absorb
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
import VerifiedGarbage.Proof.AesGcm.X86_64.OneBlocks.Facts
import VerifiedGarbage.Proof.AesGcm.X86_64.Env
import VerifiedGarbage.Proof.AesGcm.X86_64.OneBlocks.Piece
meta import VerifiedGarbage.Impl.AesGcm.X86_64.Contiguous

/-! The contiguous bulk caller supplies both cursors to the fused encryption
and authentication routine. -/
@[expose] public section
namespace VG.Proof.AesGcm.X86_64.ContiguousSeal
open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Spec.Gcm (blocksAt blockAt ctr32 ctxH ctxCiph ghashFrom inc32)
open Split (SealRegions callWr)

theorem fusedArgs_ok {Ctx St W SP : Addr} {R : Nat} {D S : Addr} {s : State} (he : Env Ctx St W SP s)
    (hR : RoundsAt s.mem W R) (read : InRegions (s.rd++s.wr) (SP+8#64) 8) (src : s.mem.readW (SP+8#64) 64 = S)
    (hdat : s.mem.readW (W + BitVec.ofNat 64 200) 64 = D) :
    WP isa (.block Contiguous.fusedArgs) s fun s₂ => s₂.gpr .rdi = Ctx ∧ s₂.gpr .rsi = BitVec.ofNat 64 R ∧
      s₂.gpr .rdx = St + BitVec.ofNat 64 48 ∧
      s₂.gpr .rcx = St + BitVec.ofNat 64 16 ∧ s₂.gpr .r8 = S ∧ s₂.gpr .r9 = s.gpr .rax ∧
      s₂.gpr .r10 = D ∧ s₂.gpr .rax = W + BitVec.ofNat 64 448 ∧
      (∀ r, r ≠ .rdi → r ≠ .rsi → r ≠ .rdx → r ≠ .rcx → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .rax → s₂.gpr r = s.gpr r) ∧
      s₂.mem = s.mem ∧ s₂.rd = s.rd ∧ s₂.wr = s.wr := by
  obtain q₁ := he.perm.wR (show 176 + 8 ≤ 2560 by decide)
  obtain q₂ := he.perm.wR (show 200 + 8 ≤ 2560 by decide)
  unfold Contiguous.fusedArgs
  apply WP.of_runBlock
  refine ⟨_, by xrun [Contiguous.src, he.rsp, he.r13, he.r14, he.r15, read, src, q₁, q₂, hR.1, hdat], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [gpr_setReg]
  · simp [gpr_setReg]
  · simp [gpr_setReg]
  · simp [gpr_setReg]
  · simp [gpr_setReg]
  · simp [gpr_setReg]
  · simp [gpr_setReg]
  · simp [gpr_setReg, bScrO]
  · intro r a b c d e f g i; simp [gpr_setReg, a, b, c, d, e, f, g, i]
  all_goals simp [mem_arithFlags, mem_setReg, rd_arithFlags, rd_setReg, wr_arithFlags, wr_setReg]

theorem fused_ok {M : CtxMode} (T : BlocksTo.SealFn M) {Ctx W SP D S : Addr} {R n q : Nat} {s : State}
    (h : SealRegions M Ctx W SP D S R n n s) (hq : 16*q ≤ n)
    (qreg : s.gpr .rax = BitVec.ofNat 64 q)
    (read : InRegions (s.rd++s.wr) (SP+8#64) 8) (src : s.mem.readW (SP+8#64) 64 = S)
    (dst : s.mem.readW (W+200#64) 64 = D) :
    WP isa (Contiguous.fused T.fn) s fun t =>
      (∀ r ∈ calleeSaved, t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      Frame (callWr W D q ++ [below SP 24]) s.mem t.mem ∧
      blocksAt t.mem D q = ctr32 (ctxCiph s.mem Ctx R) (blockAt s.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48))
        (blocksAt s.mem S q) ∧
      blockAt t.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48) =
        Nat.repeat inc32 q (blockAt s.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48)) ∧
      blockAt t.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16) =
        ghashFrom (ctxH s.mem Ctx) (blockAt s.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16)) (blocksAt t.mem D q) := by
  unfold Contiguous.fused Contiguous.call
  apply WP.seq
  refine WP.mono (fusedArgs_ok h.env h.rounds read src dst) fun x ⟨k,r,c,y,i,qx,o,w,regs,mem,rd,wr⟩ => ?_
  have keep (z : Reg) (hz : z ∈ calleeSaved) : x.gpr z = s.gpr z := by
    simp only [calleeSaved,List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> apply regs <;> decide
  refine WP.mono (Split.Compact.compactCall_ok h T hq (st:=x)
    ((keep _ (by decide)).trans h.env.rsp) rd wr mem k r c y i (qx.trans qreg) o w)
    fun t ⟨saved,dr,dw,fr,bl,ctr,hash⟩ => ?_
  exact ⟨fun z hz => (saved z hz).trans (keep z hz), dr.trans rd, dw.trans wr, mem ▸ fr, bl, ctr, hash⟩

theorem bulk_core (kernel : Prog isa) {M : CtxMode} {Ctx W SP : Addr} (L : Lay Ctx (W+16#64) W SP) {R : Nat} {D : Addr} {n : Nat} {s : State} (h : ObPre M Ctx W SP R D n s)
    {Out : State → State → Prop}
    (hframe : ∀ s₁, n/16 ≠ 0 → s₁.gpr .rax = BitVec.ofNat 64 (n/16) →
      s₁.mem = s.mem.writeW (W+192#64) (BitVec.ofNat 64 n) → s₁.rd = s.rd → s₁.wr = s.wr →
      Env Ctx (W+16#64) W SP s₁ → RoundsAt s₁.mem W R → s₁.mem.readW (W+200#64) 64 = D →
      WP isa kernel s₁ fun s₄ =>
        (∀ r ∈ calleeSaved, s₄.gpr r = s₁.gpr r) ∧ s₄.rd = s₁.rd ∧ s₄.wr = s₁.wr ∧
        Frame (obFrame (W+16#64) W SP D (n/16)) s₁.mem s₄.mem ∧ Out s₁ s₄)
    (h0 : n / 16 = 0 → ∀ s₁, s₁.mem = s.mem.writeW (W + BitVec.ofNat 64 192) (BitVec.ofNat 64 n) → Out s s₁)
    (hout : ∀ s₂ s₄ s₅, s₂.mem = s.mem.writeW (W + BitVec.ofNat 64 192) (BitVec.ofNat 64 n) → Out s₂ s₄ →
      Frame [⟨W + BitVec.ofNat 64 200, 16⟩] s₄.mem s₅.mem → Out s s₅) :
    WP isa (Contiguous.bulk kernel) s fun s' => ObPost Ctx W SP D n s s' ∧ Out s s' := by
  unfold Contiguous.bulk
  have hn : n < 2 ^ 64 := h.data.ok.lt
  have he := h.env
  obtain ⟨e176, e200, e208, -, -, -, -, -, f192⟩ := w192_eqs L h (BitVec.ofNat 64 n)
  refine WP.seq (WP.mono (ob1_ok hn he h.len) fun s₁ ⟨r₁, z₁, g₁, m₁, rd₁, wr₁⟩ => ?_)
  have he₁ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact g₁ _ (by decide)) rd₁ wr₁
  have t₁ : s₁.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 n := by rw [m₁, Mem.readW_writeW_self64]
  have hf₁ : Frame (⟨W + BitVec.ofNat 64 192, 24⟩ :: obFrame (W + BitVec.ofNat 64 16) W SP D (n / 16)) s.mem s₁.mem := by
    rw [m₁]; exact f192.mono fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact List.mem_cons_self ..
  refine WP.ite (decide (n / 16 = 0)) (by simp only [eval, z₁]) (fun hz => ?_) (fun hz => ?_)
  · simp only [decide_eq_true_eq] at hz
    refine WP.block_nil ⟨⟨he₁, rd₁, wr₁, hf₁, t₁, ?_, ?_⟩, h0 hz s₁ m₁⟩
    · rw [m₁, e200, h.dat, hz]; simp
    · rw [m₁, e208, h.len]; congr 1; omega_using [hz]
  · simp only [decide_eq_false_iff_not] at hz
    have hR₁ : RoundsAt s₁.mem W R := ⟨by rw [m₁, e176]; exact h.rounds.1, h.rounds.2⟩
    have hd₁ : s₁.mem.readW (W + BitVec.ofNat 64 200) 64 = D := by rw [m₁, e200, h.dat]
    refine WP.seq (WP.mono (hframe s₁ hz r₁ m₁ rd₁ wr₁ he₁ hR₁ hd₁) fun s₄ ⟨cs₄,rd₄,wr₄,fr₄,o₄⟩ => ?_)
    have he₄ := he₁.of_saved cs₄ rd₄ wr₄
    have kp : ∀ d, 176 ≤ d → d + 8 ≤ 240 →
        s₄.mem.readW (W + BitVec.ofNat 64 d) 64 = s₁.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d h₁ h₂ => by
      rw [fr₄.readW (Region.contains_self _ _) (ob_slots L h.data.ok.w (by omega_using []) h.t_w h₁ h₂) (by decide)]
    have hd₄ : s₄.mem.readW (W + BitVec.ofNat 64 200) 64 = D := by rw [kp 200 (by decide) (by decide), hd₁]
    have hl₄ : s₄.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 n := by
      rw [kp 208 (by decide) (by decide), m₁, e208, h.len]
    refine WP.mono (ob3_ok hn he₄ hd₄ hl₄) fun s₅ ⟨g₅, d₅, l₅, f₅, rd₅, wr₅⟩ => ?_
    have he₅ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₅ := he₄.keep (fun r hr => g₅ r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide)) rd₅ wr₅
    refine ⟨⟨he₅, rd₅.trans (rd₄.trans rd₁), wr₅.trans (wr₄.trans wr₁), ?_, ?_, d₅, l₅⟩,
      hout s₁ s₄ s₅ m₁ o₄ f₅⟩
    · refine hf₁.trans ?_
      refine (fr₄.mono fun r hr => List.mem_cons_of_mem _ hr).trans ?_
      exact f₅.sub fun r hr => ⟨_, List.mem_cons_self .., by
        simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub _ (by decide) (by decide)⟩
    · rw [f₅.readW (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact L.w_w (.inl (by decide)) (by decide) (by decide)) (by decide),
        kp 192 (by decide) (by decide), t₁]


/-- Both layouts read the plaintext from the original state at `S` and
authenticate the ciphertext written to `D`. -/
def BlocksResult (Ctx W : Addr) (R : Nat) (S D : Addr) (q : Nat) (s t : State) (hash : Bool := true) : Prop :=
  blocksAt t.mem D q = ctr32 (ctxCiph s.mem Ctx R) (blockAt s.mem (cbA W)) (blocksAt s.mem S q) ∧
  blockAt t.mem (cbA W) = Nat.repeat inc32 q (blockAt s.mem (cbA W)) ∧
  blockAt t.mem (yA W) = ghashFrom (ctxH s.mem Ctx) (blockAt s.mem (yA W)) (if hash then blocksAt t.mem D q else [])

theorem bulk_ok {M : CtxMode} (kernel : Prog isa) {hash : Bool} {Ctx W SP S D : Addr} {R n : Nat} {s : State}
    (op : ∀ {u : State}, SealRegions M Ctx W SP D S R n n u → u.gpr .rax = BitVec.ofNat 64 (n/16) →
      InRegions (u.rd++u.wr) (SP+8#64) 8 → u.mem.readW (SP+8#64) 64 = S →
      u.mem.readW (W+200#64) 64 = D → u.mem.readW (W+208#64) 64 = BitVec.ofNat 64 n →
      WP isa kernel u fun t => (∀ z ∈ calleeSaved, t.gpr z = u.gpr z) ∧ t.rd=u.rd ∧ t.wr=u.wr ∧
        Frame (obFrame (W+16#64) W SP D (n/16)) u.mem t.mem ∧ BlocksResult Ctx W R S D (n/16) u t hash)
    (h : SealRegions M Ctx W SP D S R n n s) (ob : ObPre M Ctx W SP R D n s)
    (src : s.mem.readW (SP+8#64) 64 = S) (slot : InRegions (s.rd++s.wr) (SP+8#64) 8)
    (apart : (⟨SP+8#64,8⟩ : Region).Disjoint ⟨W,2560⟩) :
    WP isa (Contiguous.bulk kernel) s fun t =>
      ObPost Ctx W SP D n s t ∧ BlocksResult Ctx W R S D (n/16) s t hash := by
  let v := BitVec.ofNat 64 n
  let w := W+BitVec.ofNat 64 192
  have ww : Region.Sub ⟨w,8⟩ ⟨W,2560⟩ := Lay.wSub (by decide)
  have writeFrame : Frame [⟨w,8⟩] s.mem (s.mem.writeW w v) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have one {r : Region} (sep : r.Disjoint ⟨W,2560⟩) : ∀ b ∈ [(⟨w,8⟩ : Region)], r.Disjoint b := by
    intro b hb; obtain rfl := List.mem_singleton.mp hb; exact sep.sub_right ww
  obtain ⟨-, -, eN, eK, eC, eY, -, eH, -⟩ := w192_eqs h.lay ob v
  have eS : blocksAt (s.mem.writeW w v) S (n / 16) = blocksAt s.mem S (n / 16) :=
    blocksAt_frame writeFrame (one (h.sW.sub_left (Region.sub_prefix (by omega_arith)))) (by have := h.sWrap; omega_arith)
  dsimp only [v,w] at eK eC eY eH eS eN
  refine bulk_core (Out := fun a b => BlocksResult Ctx W R S D (n/16) a b hash) _ h.lay ob (fun u _ q mem rd wr env rounds dst => ?_) (fun hz u m => ?_) (fun u t z m o fr => ?_)
  · have ext := h.ext.keep rd wr (by rw [mem]; exact writeFrame) (one h.ext.cw)
    have input : SealRegions M Ctx W SP D S R n n u :=
      { h with env := env, rounds := rounds, data := h.data.of_eq rd wr, srcCov := by rw [rd,wr]; exact h.srcCov, ext := ext }
    exact op input q (by rw [rd,wr]; exact slot)
      (by rw [mem,writeFrame.readW (Region.contains_self _ _) (one apart) (by decide)]; exact src) dst (by rw [mem,eN,ob.len])
  · rw [BlocksResult,hz,m,eC,eY]; cases hash <;> exact ⟨rfl,rfl,rfl⟩
  · obtain ⟨b,c,y⟩ := ob_after h.lay ob fr
    obtain ⟨ob,oc,oy⟩ := o
    simp only [ctxCiph,ctxH,m,eK,eC,eY,eH,eS] at ob oc oy
    exact ⟨b.trans ob,c.trans oc,by rw [y,b]; exact oy⟩

theorem fused_bulk_ok {M : CtxMode} (T : BlocksTo.SealFn M) {Ctx W SP S D : Addr} {R n : Nat} {s : State}
    (h : SealRegions M Ctx W SP D S R n n s) (ob : ObPre M Ctx W SP R D n s)
    (src : s.mem.readW (SP+8#64) 64 = S) (slot : InRegions (s.rd++s.wr) (SP+8#64) 8)
    (apart : (⟨SP+8#64,8⟩ : Region).Disjoint ⟨W,2560⟩) :
    WP isa (Contiguous.bulk (Contiguous.fused T.fn)) s fun t =>
      ObPost Ctx W SP D n s t ∧ BlocksResult Ctx W R S D (n/16) s t := by
  exact bulk_ok (hash:=true) _ (fun hu q read origin dest _ => fused_ok T hu (Nat.mul_div_le n 16) q read origin dest) h ob src slot apart

end VG.Proof.AesGcm.X86_64.ContiguousSeal
