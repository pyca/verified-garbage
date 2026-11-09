module

-- separate module: its proofs build in parallel with `RndReject`'s, which `RndVerified` also imports

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.RndScan
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.RndEnc
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.PcVerified
import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.RndTaint
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.Instr
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.Loops
import VerifiedGarbage.Proof.RsaPkcs1Sig.BytesAt
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem

/-!
# RSAES-PKCS1-v1_5 encryption from a random tape on x86: `PS` drawn

With `PS` full: the tape's words (`tapePtr_vp`, `tapeAcc_vp`), the callee's
fourteen arguments at the frame's base (`callArgs_vp`), the call of
`vg_rsa_pkcs1_encrypt_precomputed` by its contract (`call_vp`), the status
`2 - r` (`status_vp`) and `PS` wiped (`wipe_vp`): what the function writes
and returns (`Res`, `accept_vp`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.X86.Rnd

open VG VG.Impl.RsaPkcs1Enc.X86.Random VG.Proof.RsaPkcs1Sig.X86
open VG.X86 hiding frameBytes
open VG.X86.Wp

variable {P : RP}

theorem S.nB' {σ s : State} (hs : S P σ s) : Spec.Rsa.bytesAt s.mem (P.n.setWidth 64) P.K = P.nB :=
  (hs.2.ro (R := P.N) (by simp)).trans hs.1.nB

theorem S.eB' {σ s : State} (hs : S P σ s) : Spec.Rsa.bytesAt s.mem (P.e.setWidth 64) P.el = P.eB :=
  (hs.2.ro (R := P.E) (by simp)).trans hs.1.eB

theorem S.pw' {σ s : State} (hs : S P σ s) : Spec.Rsa.wordsAt s.mem (P.pre.setWidth 64) P.rl = P.pw := by
  have ok := hs.1.ok
  have hR : P.PRE ∈ P.lay.ro := by simp
  have hf : (P.pre.setWidth 64).toNat + P.rl * 8 ≤ 2 ^ 32 := ok.fits P.PRE (List.mem_append_left _ hR)
  refine (Proof.RsaPkcs1Sig.wordsAt_frame' hs.2.frame (fun r hr => ?_) (by omega)).trans hs.1.pw
  simp only [Lay.W, List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil, or_false,
    false_or] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact ((ok.stk P.PRE (List.mem_append_left _ hR)).sub_left Lay.FR_stk).symm
  · exact (ok.wro P.OUT (by simp) P.PRE (List.mem_append_left _ hR)).symm
  · exact (ok.wro P.TAPE (by simp) P.PRE (List.mem_append_left _ hR)).symm
  · exact (ok.wro P.SCR (by simp) P.PRE (List.mem_append_left _ hR)).symm
  · exact ((ok.stk P.PRE (List.mem_append_left _ hR)).sub_left Lay.low_stk).symm

/-- The tape's words, kept by memory that changed apart from the tape. -/
theorem TapeW.frame {σ s : State} (hs : S P σ s) {m m' : Mem} {u v : Nat} (h : TapeW P m u v) {rs : List Region}
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, Region.Disjoint P.TAPE r) : TapeW P m' u v := by
  have := hs.1.tape_fit
  rw [TapeW, Proof.RsaPkcs1Sig.wordsAt_frame' hf (by simpa using hd) (by omega)]; exact h

/-- `PS` drawn, as bytes. -/
theorem Kept.bytes {σ s : State} (hs : S P σ s) (h : Kept P σ s P.mask.length)
    (hc : cnt P.mask P.mask.length = P.pl) : Spec.Rsa.bytesAt s.mem (P.lay.fr oBuf) P.pl = psv P σ := by
  have hl : (psv P σ).length = P.pl := by rw [hs.1.cntE (Nat.le_refl _), hc]
  rw [← hl]
  refine Proof.RsaPkcs1Sig.bytesAt_eq fun i hi => ?_
  rw [Offset.add_ofNat_add_ofNat]
  exact h i (by rw [hc, ← hl]; exact hi)

/-! ## The tape -/

/-- With `PS` full, and the tape's pointer in `eax`. -/
structure AC1 (P : RP) (σ s : State) : Prop where
  hs : S P σ s
  cx : s.gpr .ecx = BitVec.ofNat 32 (P.len - P.mask.length)
  kept : Kept P σ s P.mask.length
  full : cnt P.mask P.mask.length = P.pl
  ax : s.gpr .eax = P.tape

/-- The tape written. -/
structure AC2 (P : RP) (σ s : State) : Prop where
  hs : S P σ s
  kept : Kept P σ s P.mask.length
  full : cnt P.mask P.mask.length = P.pl
  tape : TapeW P s.mem P.mask.length 0

theorem tapePtr_vp : VP (fun σ s => Dz P σ s ∧ isa.eval .e s = some true) (.block tapePtr) (AC1 P) :=
  VP.taint [.esp] tapePtr_taint (sp_agree fun _ _ h => h.1.1.hs) fun σ s ⟨⟨h, z⟩, he⟩ => by
    have hc : cnt P.mask P.mask.length = P.pl := by
      change s.zf = _ at he; rw [z] at he; simpa using he
    simp only [tapePtr]
    refine h.hs.2.wp_arg (j := 2) (r := .eax) (by simp) (by decide) fun t st u => WP.block_nil ?_
    exact ⟨⟨h.hs.1, st⟩, by rw [u.other _ (by decide)]; exact h.cx, fun i hi => by rw [u.mem]; exact h.kept i hi,
      hc, u.gpr⟩

theorem tapeAcc_wp {σ s : State} (h : AC1 P σ s) : WP isa (.block tapeAcc) s (AC2 P σ) := by
  have hs := h.hs
  have hN := hs.1.len_N
  have hl := hs.1.len1149
  have hpl := hs.1.pl1021
  simp only [tapeAcc]
  refine hs.2.wp_arg (j := 10) (r := .ebx) (by simp) (by decide) fun t1 s1 u1 => ?_
  refine wp_sub fun t2 u2 _ => ?_
  have s2 : S P σ t2 := ⟨hs.1, s1.upd u2 (by decide)⟩
  have ax2 : t2.gpr .eax = P.tape := by rw [u2.other _ (by decide), u1.other _ (by decide), h.ax]
  have bx2 : t2.gpr .ebx = BitVec.ofNat 32 P.mask.length := by
    rw [u2.gpr, u1.gpr, u1.other _ (by decide), h.cx]
    show BitVec.ofNat 32 P.len - _ = _
    rw [sub_ofNat (by omega)]; congr 1; omega
  refine wp_stTape s2 (o := 0) (by decide) ax2 fun t3 s3 g3 m3 f3 => ?_
  refine wp_movi fun t4 u4 => ?_
  have s4 : S P σ t4 := ⟨hs.1, s3.2.upd u4 (by decide)⟩
  have ax4 : t4.gpr .eax = P.tape := by rw [u4.other _ (by decide), g3, ax2]
  refine wp_stTape s4 (o := 4) (by decide) ax4 fun t5 s5 g5 m5 f5 => ?_
  refine wp_stTape s5 (o := 8) (by decide) (by rw [g5, ax4]) fun t6 s6 g6 m6 f6 => ?_
  refine wp_stTape s6 (o := 12) (by decide) (by rw [g6, g5, ax4]) fun t7 s7 g7 m7 f7 => WP.block_nil ?_
  have mm : t7.mem = (((t2.mem.writeW (P.tape.setWidth 64) (BitVec.ofNat 32 P.mask.length)).writeW
      (P.tape.setWidth 64 + BitVec.ofNat 64 4) (0 : BitVec 32)).writeW (P.tape.setWidth 64 + BitVec.ofNat 64 8)
      (0 : BitVec 32)).writeW (P.tape.setWidth 64 + BitVec.ofNat 64 12) (0 : BitVec 32) := by
    rw [m7, m6, m5, u4.mem, m3, BitVec.add_zero, g6, g5, u4.gpr, bx2]
  have hk : Kept P σ t7 P.mask.length := by
    have k2 : Kept P σ t2 P.mask.length := fun i hi => by rw [u2.mem, u1.mem]; exact h.kept i hi
    have f4 : Frame [P.TAPE] t3.mem t4.mem := by rw [u4.mem]; exact Frame.refl _ _
    exact Kept.frame k2 (by rw [h.full]) hpl (f3.trans (f4.trans (f5.trans (f6.trans f7)))) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hs.1.buf_tape)
  refine ⟨s7, hk, h.full, ?_⟩
  rw [TapeW, mm, words4, zero_append_ofNat (by omega), show (0 : BitVec 32) ++ (0 : BitVec 32) = BitVec.ofNat 64 0
    by decide]

theorem tapeAcc_vp : VP (AC1 P) (.block tapeAcc) (AC2 P) :=
  VP.taint [.esp, .eax, .ecx] tapeAcc_taint (fun _ _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [h₁.hs.2.sp, h₂.hs.2.sp]
      · rw [h₁.ax, h₂.ax]
      · rw [h₁.cx, h₂.cx]) fun _ _ h => tapeAcc_wp h

/-! ## The call's arguments -/

/-- The callee's arguments. -/
abbrev cargs (P : RP) : List (BitVec 32) :=
  encArgv P.out P.n P.e P.msg (P.B + BitVec.ofNat 32 oBuf) P.scr P.pre P.K P.el P.ml P.pl P.sl P.rl

/-- The first `k` of them in place. -/
def Slots (P : RP) (m : Mem) (k : Nat) : Prop :=
  ∀ i < k, m.readW (P.lay.fr (4 * i)) 32 = (cargs P).getD i 0

/-- Before the call. -/
abbrev AC3 (P : RP) (σ s : State) : Prop := AC2 P σ s ∧ Slots P s.mem 14

theorem AC2.upd {σ s t : State} (h : AC2 P σ s) {d : Reg} {v : BitVec 32} (u : Upd s t d v) (hd : d ≠ .esp) :
    AC2 P σ t :=
  ⟨⟨h.hs.1, h.hs.2.upd u hd⟩, fun i hi => by rw [u.mem]; exact h.kept i hi, h.full, by rw [TapeW, u.mem]; exact h.tape⟩

/-- `mov [esp + 4 i], eax`: the call's argument `i`. -/
theorem slotStore {σ s : State} {i : Nat} (h : AC2 P σ s) (hsl : Slots P s.mem i) (hi : i < 14)
    (hv : s.gpr .eax = (cargs P).getD i 0) {is : List Instr} {Q : State → Prop}
    (kk : ∀ t, AC2 P σ t → Slots P t.mem (i + 1) → WP isa (.block is) t Q) :
    WP isa (.block (.store (Impl.RsaPkcs1Sig.X86.stk (4 * i)) .eax :: is)) s Q := by
  have hpl := h.hs.1.pl1021
  refine h.hs.2.wp_strFr (d := 4 * i) (by show 4 * i + 4 ≤ frameBytes; simp only [frameBytes]; omega)
    fun t s2 m2 => kk t ⟨⟨h.hs.1, s2⟩, ?_, h.full, ?_⟩ ?_
  · refine Kept.frame h.kept (by rw [h.full]) hpl (rs := [⟨P.lay.fr (4 * i), 4⟩]) ?_ fun r hr => ?_
    · rw [m2.mem]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
    · simp only [List.mem_singleton] at hr; subst hr
      exact Lay.fr_sep (by simp only [oBuf]; omega) (by simp only [oBuf]; omega) (by omega)
  · refine TapeW.frame h.hs h.tape (rs := [⟨P.lay.fr (4 * i), 4⟩]) ?_ fun r hr => ?_
    · rw [m2.mem]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
    · simp only [List.mem_singleton] at hr; subst hr
      exact (h.hs.1.ok.stk_fr (R := P.TAPE) (.inr (by simp)) (by show _ ≤ frameBytes + 16; simp only [frameBytes]; omega)).symm
  · intro k hk
    rw [m2.mem]
    rcases (by omega : k = i ∨ k < i) with rfl | hki
    · rw [Mem.readW_writeW_self32, hv]
    · rw [Lay.readW_fr_other _ _ _ (by omega) (by omega) (by omega)]
      exact hsl k hki

/-- Argument `j` to the call's argument `i`. -/
theorem copySlot {σ s : State} {i j : Nat} (h : AC2 P σ s) (hsl : Slots P s.mem i) (hi : i < 14)
    (hj : j < 15) (hv : P.argv.getD j 0 = (cargs P).getD i 0) {is : List Instr} {Q : State → Prop}
    (kk : ∀ t, AC2 P σ t → Slots P t.mem (i + 1) → WP isa (.block is) t Q) :
    WP isa (.block (copyArg j i ++ is)) s Q :=
  h.hs.2.wp_arg (j := j) (by simp only [RP.argv, List.length_cons, List.length_nil]; omega) (by decide)
    fun t1 _ u1 => slotStore (h.upd u1 (by decide)) (fun k hk => by rw [u1.mem]; exact hsl k hk) hi
      (by rw [u1.gpr, hv]) kk

theorem callArgs_wp {σ s : State} (h : AC2 P σ s) : WP isa (.block callArgs) s (AC3 P σ) := by
  simp only [callArgs, List.append_assoc, List.cons_append, List.nil_append]
  have z0 : Slots P s.mem 0 := fun _ hi => absurd hi (Nat.not_lt_zero _)
  refine copySlot h z0 (by decide) (j := 0) (by decide) rfl fun t1 h1 z1 => ?_
  refine copySlot h1 z1 (by decide) (j := 4) (by decide) rfl fun t2 h2 z2 => ?_
  refine copySlot h2 z2 (by decide) (j := 3) (by decide) rfl fun t3 h3 z3 => ?_
  refine copySlot h3 z3 (by decide) (j := 4) (by decide) rfl fun t4 h4 z4 => ?_
  refine copySlot h4 z4 (by decide) (j := 5) (by decide) rfl fun t5 h5 z5 => ?_
  refine copySlot h5 z5 (by decide) (j := 6) (by decide) rfl fun t6 h6 z6 => ?_
  refine copySlot h6 z6 (by decide) (j := 7) (by decide) rfl fun t7 h7 z7 => ?_
  refine copySlot h7 z7 (by decide) (j := 8) (by decide) rfl fun t8 h8 z8 => ?_
  refine wp_mov fun t9 u9 => wp_addi fun t10 u10 => ?_
  have h10 := (h8.upd u9 (by decide)).upd u10 (by decide)
  refine slotStore (i := 8) h10 (fun k hk => by rw [u10.mem, u9.mem]; exact z8 k hk) (by decide)
    (by rw [u10.gpr, u9.gpr, h8.hs.2.sp]; rfl) fun t11 h11 z11 => ?_
  refine wp_psLen h11.hs (r := .eax) (t := .ebx) (by decide) (by decide) (by decide) fun t12 s12 a12 _ m12 => ?_
  have h12 : AC2 P σ t12 := ⟨s12, fun i hi => by rw [m12]; exact h11.kept i hi, h11.full, by rw [TapeW, m12]; exact h11.tape⟩
  refine slotStore (i := 9) h12 (fun k hk => by rw [m12]; exact z11 k hk) (by decide) (by rw [a12]; rfl)
    fun t13 h13 z13 => ?_
  refine copySlot h13 z13 (by decide) (j := 11) (by decide) rfl fun t14 h14 z14 => ?_
  refine copySlot h14 z14 (by decide) (j := 12) (by decide) rfl fun t15 h15 z15 => ?_
  refine copySlot h15 z15 (by decide) (j := 13) (by decide) rfl fun t16 h16 z16 => ?_
  refine copySlot h16 z16 (by decide) (j := 14) (by decide) rfl fun t17 h17 z17 => ?_
  exact WP.block_nil ⟨h17, z17⟩

theorem callArgs_vp : VP (AC2 P) (.block callArgs) (AC3 P) :=
  VP.taint [.esp] callArgs_taint (sp_agree fun _ _ h => h.hs) fun _ _ h => callArgs_wp h

/-! ## The call -/

/-- What the call writes and returns. -/
def CR (P : RP) (σ : State) (m : Mem) (r : BitVec 32) : Prop :=
  Spec.Rsa.publicPrecompute P.nB = some P.pw →
    Spec.Rsa.written m (P.out.setWidth 64) P.K r (Spec.RsaPkcs1Enc.encrypt P.nB P.eB (msgB P σ) (psv P σ))

/-- After the call. -/
structure AC4 (P : RP) (σ s : State) : Prop where
  hs : S P σ s
  full : cnt P.mask P.mask.length = P.pl
  tape : TapeW P s.mem P.mask.length 0
  cr : CR P σ s.mem (s.gpr .eax)

theorem pcStack_eq (c : Ver.PublicImpl) :
    stackUse (Impl.RsaPkcs1Enc.X86.Precomputed.code c.name c.code) = stackUse c.code + 4 + 1072 + 16 := by
  simp only [Impl.RsaPkcs1Enc.X86.Precomputed.code, Impl.RsaPkcs1Sig.X86.wrap,
    Impl.RsaPkcs1Enc.X86.Precomputed.body, Impl.RsaPkcs1Enc.X86.Precomputed.psLoop,
    Impl.RsaPkcs1Enc.X86.Precomputed.msgCopy, Impl.RsaPkcs1Enc.X86.Precomputed.maskLoop,
    Impl.RsaPkcs1Enc.X86.Precomputed.zeroLoop, Impl.Bignum.X86.copyBytes, stackUse, VG.X86.frameBytes,
    Impl.RsaPkcs1Sig.X86.savedRegs, List.length_cons, List.length_nil, Impl.RsaPkcs1Enc.X86.Precomputed.frameBytes,
    Nat.zero_max, Nat.max_zero, Nat.max_self]

theorem pcStack (c : Ver.PublicImpl) :
    stackUse (Impl.RsaPkcs1Enc.X86.Precomputed.code c.name c.code) ≤ encStack := by
  rw [pcStack_eq]
  have := c.stack
  simp only [encStack]
  omega

theorem AC3.encArgs {σ s : State} (h : AC3 P σ s) :
    EncArgs s P.out P.n P.e P.msg (P.B + BitVec.ofNat 32 oBuf) P.scr P.pre P.K P.el P.ml P.pl P.sl P.rl := by
  obtain ⟨⟨hs, -, -, -⟩, sl⟩ := h
  have fit := hs.1.fit
  have hsp : s.gpr .esp = P.B := hs.2.sp
  refine ⟨fun i hi => ?_, ?_, ?_, hs.1.kv, hs.1.el1, hs.1.elK, hs.1.mlK, rfl, hs.1.slK, hs.1.sl32, hs.1.rlK⟩
  · have hd : 4 * i < P.lay.F + 20 + P.lay.A := by
      simp only [Lay.A, RP.argv, List.length_cons, List.length_nil, frameBytes] at fit ⊢; omega
    rw [hsp, hs.1.ok.addrB hd]
    exact sl i hi
  · rw [hsp]; exact hs.1.ok.BC
  · rw [hsp]; simp only [frameBytes] at fit; omega

/-- The call's arguments, at the frame's base. -/
theorem argsA (P : RP) : (⟨P.B.setWidth 64, 56⟩ : Region) = ⟨P.lay.fr 0, 56⟩ := by simp

theorem written_congr {m m' : Mem} {a : Addr} {K : Nat} {r : BitVec 32} {o : Option (List Byte)}
    (hb : Spec.Rsa.bytesAt m' a K = Spec.Rsa.bytesAt m a K) (h : Spec.Rsa.written m a K r o) :
    Spec.Rsa.written m' a K r o := by
  cases o with
  | some y => exact ⟨h.1, hb.trans h.2⟩
  | none => exact ⟨h.1, hb.trans h.2⟩

theorem call_vp (encName : String) (c : Ver.PublicImpl) :
    VP (AC3 P) (.call encName (Impl.RsaPkcs1Enc.X86.Precomputed.code c.name c.code)) (AC4 P) := by
  have hv := Pc.code_verified c
  refine VP.call (k := Proof.RsaPkcs1Enc.encryptPrecomputedContract abi encStack) hv.1 hv.2.1 (Pc.code_noSp c)
    (encRd P.n P.e P.msg (P.B + BitVec.ofNat 32 oBuf) P.pre P.K P.el P.ml P.pl P.rl) (encWr P.B P.out P.scr P.K P.sl)
    (fun σ s h => ?_) (fun σ s h => ?_) (fun σ s h => ?_)
    (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.1.hs.2.sp, h₂.1.hs.2.sp]) (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => ?_)
    (fun σ s s' h rd wr cs fr po => ?_)
  · -- The callee's precondition.
    have hs := h.1.hs
    have ok := hs.1.ok
    have hpl := hs.1.pl1021
    have fit := hs.1.fit
    have hsp : s.gpr .esp = P.B := hs.2.sp
    have hb := hs.1.bufA
    have ar := argsA P
    have hfr : ∀ d, d ≤ frameBytes → (P.lay.fr d).toNat = P.B.toNat + d := fun d hd =>
      Lay.fr_toNat (by simp only [Lay.A, RP.argv, List.length_cons, List.length_nil] at fit ⊢; omega)
        (by simp only [Lay.A, RP.argv, List.length_cons, List.length_nil]; omega)
    have := enc_pre h.encArgs ?_ ?_ ?_ ?_
    · rw [hsp] at this; exact this
    all_goals rw [hsp]
    · intro w hw r hr
      simp only [encWr, encRd, List.mem_cons, List.not_mem_nil, or_false] at hw hr
      rcases hw with rfl | rfl | rfl <;> rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact ok.rw_ro (w := P.OUT) (by simp) (r := P.N) (by simp)
      · exact ok.rw_ro (w := P.OUT) (by simp) (r := P.E) (by simp)
      · exact ok.rw_ro (w := P.OUT) (by simp) (r := P.MSG) (by simp)
      · rw [hb]; exact (ok.stk_fr (R := P.OUT) (.inr (by simp)) (by simp only [oBuf, frameBytes]; omega)).symm
      · exact ok.rw_ro (w := P.OUT) (by simp) (r := P.PRE) (by simp)
      · exact ok.rw_ro (w := P.SCR) (by simp) (r := P.N) (by simp)
      · exact ok.rw_ro (w := P.SCR) (by simp) (r := P.E) (by simp)
      · exact ok.rw_ro (w := P.SCR) (by simp) (r := P.MSG) (by simp)
      · rw [hb]; exact (ok.stk_fr (R := P.SCR) (.inr (by simp)) (by simp only [oBuf, frameBytes]; omega)).symm
      · exact ok.rw_ro (w := P.SCR) (by simp) (r := P.PRE) (by simp)
      · rw [ar]; exact ok.stk_fr (R := P.N) (.inl (by simp)) (by simp only [frameBytes]; omega)
      · rw [ar]; exact ok.stk_fr (R := P.E) (.inl (by simp)) (by simp only [frameBytes]; omega)
      · rw [ar]; exact ok.stk_fr (R := P.MSG) (.inl (by simp)) (by simp only [frameBytes]; omega)
      · rw [ar, hb]; exact Lay.fr_sep (by simp only [oBuf]; omega) (by omega) (by simp only [oBuf]; omega)
      · rw [ar]; exact ok.stk_fr (R := P.PRE) (.inl (by simp)) (by simp only [frameBytes]; omega)
    · simp only [encWr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, List.Pairwise.nil, and_true]
      have ww := ok.wrw
      simp only [RP.rw, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq] at ww
      refine ⟨⟨ww.1.2, ?_⟩, ?_⟩
      · rw [ar]; exact (ok.stk_fr (R := P.OUT) (d := 0) (n := 56) (.inr (by simp))
          (by show _ ≤ frameBytes + 16; simp only [frameBytes]; omega)).symm
      · rw [ar]; exact ⟨(ok.stk_fr (R := P.SCR) (d := 0) (n := 56) (.inr (by simp))
          (by show _ ≤ frameBytes + 16; simp only [frameBytes]; omega)).symm, fun _ h => h.elim⟩
    · intro r hr
      rw [show below P.B (encStack + 4) = P.lay.LOW from ok.low_eq]
      simp only [encWr, encRd, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact ok.low_buf (R := P.OUT) (.inr (by simp))
      · exact ok.low_buf (R := P.SCR) (.inr (by simp))
      · rw [ar]; exact (Lay.fr_low (by omega) (by show (1192 : Nat) ≤ 2 ^ 32; decide)).symm
      · exact ok.low_buf (R := P.N) (.inl (by simp))
      · exact ok.low_buf (R := P.E) (.inl (by simp))
      · exact ok.low_buf (R := P.MSG) (.inl (by simp))
      · rw [hb]; exact (Lay.fr_low (by simp only [oBuf]; omega) (by show (1192 : Nat) ≤ 2 ^ 32; decide)).symm
      · exact ok.low_buf (R := P.PRE) (.inl (by simp))
    · intro r hr
      simp only [encWr, encRd, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact ok.fits P.OUT (by simp)
      · exact ok.fits P.SCR (by simp)
      · rw [ar]; show (P.lay.fr 0).toNat + 56 ≤ _; rw [hfr 0 (by decide)]; simp only [frameBytes] at fit; omega
      · exact ok.fits P.N (by simp)
      · exact ok.fits P.E (by simp)
      · exact ok.fits P.MSG (by simp)
      · rw [hb]; show (P.lay.fr oBuf).toNat + P.pl ≤ _
        rw [hfr oBuf (by decide)]; simp only [oBuf, frameBytes] at fit ⊢; omega
      · exact ok.fits P.PRE (by simp)
  · -- What the callee is given is ours.
    have hs := h.1.hs
    have hpl := hs.1.pl1021
    have hb := hs.1.bufA
    have ar := argsA P
    have hro : ∀ R ∈ P.lay.ro, Covers [R] (s.rd ++ s.wr) := fun R hR =>
      Covers.of_mem fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hs.2.inRo hR
    have hrw : ∀ R ∈ P.lay.rw, Covers [R] s.wr := fun R hR =>
      Covers.of_mem fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hs.2.inRw hR
    have hA : Covers [⟨P.B.setWidth 64, 56⟩] s.wr := by
      rw [ar]; exact Covers.one (hs.2.inFr (by simp only [frameBytes]; omega))
    have hE : Covers [⟨(P.B + BitVec.ofNat 32 oBuf).setWidth 64, P.pl⟩] (s.rd ++ s.wr) := by
      rw [hb]; exact Covers.one (hs.2.inFrR (by simp only [oBuf, frameBytes]; omega))
    have wr : Covers (encWr P.B P.out P.scr P.K P.sl) s.wr :=
      (hrw P.OUT (by simp)).cons ((hrw P.SCR (by simp)).cons (hA.cons Covers.nil))
    exact ⟨Covers.append_left ((hro P.N (by simp)).cons ((hro P.E (by simp)).cons ((hro P.MSG (by simp)).cons
      (hE.cons ((hro P.PRE (by simp)).cons Covers.nil))))) wr.right, wr⟩
  · rw [show s.gpr .esp = P.B from h.1.hs.2.sp]
    have := h.1.hs.1.ok.BC
    have := pcStack c
    simp only [encStack] at this
    simp only [roomC] at *
    omega
  · have ok := h₁.1.hs.1.ok
    have lw : below (s₁.gpr .esp) (encStack + 4) = P.lay.LOW := by
      rw [h₁.1.hs.2.sp]; exact ok.low_eq
    refine enc_pub h₁.encArgs h₂.encArgs (by rw [h₁.1.hs.2.sp, h₂.1.hs.2.sp]) (by rw [h₁.1.hs.nB', h₂.1.hs.nB'])
      (by rw [h₁.1.hs.eB', h₂.1.hs.eB']) (by rw [h₁.1.hs.pw', h₂.1.hs.pw']) ?_ ?_ ?_ _ _
    · rw [lw]; exact ok.low_buf (R := P.N) (.inl (by simp))
    · rw [lw]; exact ok.low_buf (R := P.E) (.inl (by simp))
    · rw [lw]; exact ok.low_buf (R := P.PRE) (.inl (by simp))
  · -- After the call.
    have hh := h
    obtain ⟨⟨hs, kept, full, tape⟩, -⟩ := h
    have ok := hs.1.ok
    have hpl := hs.1.pl1021
    have hsp := hs.2.sp
    have hb := hs.1.bufA
    have ar := argsA P
    have low : Region.Sub (below (s.gpr .esp) (stackUse (Impl.RsaPkcs1Enc.X86.Precomputed.code c.name c.code) + 4))
        P.lay.LOW := by
      rw [hsp, ← ok.low_eq]
      exact below_sub (by have := pcStack c; simp only [encStack] at this; show _ ≤ 1192; omega) ok.BC
    have hw : ∀ r ∈ encWr P.B P.out P.scr P.K P.sl ++
        [below (s.gpr .esp) (stackUse (Impl.RsaPkcs1Enc.X86.Precomputed.code c.name c.code) + 4)],
        ∃ R ∈ P.lay.W, Region.Sub r R := fun r hr => by
      simp only [encWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨P.OUT, by simp, fun _ h => h⟩
      · exact ⟨P.SCR, by simp, fun _ h => h⟩
      · refine ⟨P.lay.FR, by simp, ?_⟩
        rw [ar]; exact Offset.sub_base _ (by simp only [frameBytes]; omega)
      · exact ⟨P.lay.LOW, by simp, low⟩
    have st : P.lay.St σ s' := hs.2.write fr hw rd wr (cs .esp (by simp [calleeSaved]))
    have ww := ok.wrw
    simp only [RP.rw, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at ww
    have tp : TapeW P s'.mem P.mask.length 0 := TapeW.frame hs tape fr fun r hr => by
      simp only [encWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ww.1.1.symm
      · exact ww.2.1
      · rw [ar]; exact (ok.stk_fr (R := P.TAPE) (d := 0) (n := 56) (.inr (by simp))
          (by show _ ≤ frameBytes + 16; simp only [frameBytes]; omega)).symm
      · exact (ok.low_buf (R := P.TAPE) (.inr (by simp))).symm.sub_right low
    refine ⟨⟨hs.1, st⟩, full, tp, fun hp => ?_⟩
    obtain ⟨s₂, m₂, g₂, po⟩ := po
    have := enc_post hh.encArgs po
    rw [m₂, g₂ .eax (by decide)] at this
    have hC : 4 ≤ P.lay.C := by show 4 ≤ roomC; decide
    have eN : Spec.Rsa.bytesAt s.callEntry.mem (P.n.setWidth 64) P.K = P.nB :=
      (hs.2.callEntry_ro hC (R := P.N) (by simp)).trans hs.1.nB
    have eE : Spec.Rsa.bytesAt s.callEntry.mem (P.e.setWidth 64) P.el = P.eB :=
      (hs.2.callEntry_ro hC (R := P.E) (by simp)).trans hs.1.eB
    have eM : Spec.Rsa.bytesAt s.callEntry.mem (P.msg.setWidth 64) P.ml = msgB P σ :=
      hs.2.callEntry_ro hC (R := P.MSG) (by simp)
    have eW : Spec.Rsa.wordsAt s.callEntry.mem (P.pre.setWidth 64) P.rl = P.pw := by
      have hR : P.PRE ∈ P.lay.ro := by simp
      have hf : (P.pre.setWidth 64).toNat + P.rl * 8 ≤ 2 ^ 32 := ok.fits P.PRE (List.mem_append_left _ hR)
      refine (Proof.RsaPkcs1Sig.wordsAt_frame' (hs.2.callEntry_frame hC) (fun r hr => ?_)
        (by omega)).trans hs.pw'
      simp only [List.mem_singleton] at hr; subst hr
      exact ((ok.stk P.PRE (List.mem_append_left _ hR)).sub_left Lay.low_stk).symm
    have eP : Spec.Rsa.bytesAt s.callEntry.mem ((P.B + BitVec.ofNat 32 oBuf).setWidth 64) P.pl = psv P σ := by
      rw [hb]
      refine (Proof.RsaPkcs1Sig.bytesAt_frame (hs.2.callEntry_frame hC) (fun r hr => ?_)
        (by omega)).trans (Kept.bytes hs kept full)
      simp only [List.mem_singleton] at hr; subst hr
      exact Lay.fr_low (by simp only [oBuf]; omega) (by show (1192 : Nat) ≤ 2 ^ 32; decide)
    rw [eN, eE, eM, eP, eW] at this
    exact this hp

/-! ## The status and the wipe -/

/-- The status and the wipe's registers. -/
structure AC5 (P : RP) (σ s : State) : Prop where
  hs : S P σ s
  full : cnt P.mask P.mask.length = P.pl
  tape : TapeW P s.mem P.mask.length 0
  cr : ∃ r₀, CR P σ s.mem r₀ ∧ s.gpr .ebx = 2 - r₀
  si : s.gpr .esi = P.B + BitVec.ofNat 32 oBuf
  cx : s.gpr .ecx = BitVec.ofNat 32 P.pl
  ax : s.gpr .eax = 0

/-- `PS` wiped. -/
structure AC6 (P : RP) (σ s : State) : Prop where
  hs : S P σ s
  full : cnt P.mask P.mask.length = P.pl
  tape : TapeW P s.mem P.mask.length 0
  cr : ∃ r₀, CR P σ s.mem r₀ ∧ s.gpr .ebx = 2 - r₀

theorem status_wp {σ s : State} (h : AC4 P σ s) : WP isa (.block status) s (AC5 P σ) := by
  have hs := h.hs
  simp only [status, List.cons_append, List.nil_append]
  refine wp_movi fun t1 u1 => wp_sub fun t2 u2 _ => wp_mov fun t3 u3 => wp_addi fun t4 u4 => ?_
  have s4 : S P σ t4 := ⟨hs.1, (((hs.2.upd u1 (by decide)).upd u2 (by decide)).upd u3 (by decide)).upd u4 (by decide)⟩
  refine wp_psLen s4 (r := .ecx) (t := .eax) (by decide) (by decide) (by decide) fun t5 s5 c5 o5 m5 => ?_
  refine wp_movi fun t6 u6 => WP.block_nil ?_
  have mm : t6.mem = s.mem := by rw [u6.mem, m5, u4.mem, u3.mem, u2.mem, u1.mem]
  refine ⟨⟨hs.1, s5.2.upd u6 (by decide)⟩, h.full, by rw [TapeW, mm]; exact h.tape,
    ⟨s.gpr .eax, by rw [mm]; exact h.cr, ?_⟩, ?_, ?_, u6.gpr⟩
  · rw [u6.other _ (by decide), o5 _ (by decide) (by decide), u4.other _ (by decide), u3.other _ (by decide),
      u2.gpr, u1.gpr, u1.other _ (by decide)]
  · rw [u6.other _ (by decide), o5 _ (by decide) (by decide), u4.gpr, u3.gpr, u2.other _ (by decide),
      u1.other _ (by decide), hs.2.sp]
  · rw [u6.other _ (by decide), c5]

theorem status_vp : VP (AC4 P) (.block status) (AC5 P) :=
  VP.taint [.esp] status_taint (sp_agree fun _ _ h => h.hs) fun _ _ h => status_wp h

theorem wipe_wp {σ s : State} (h : AC5 P σ s) : WP isa zeroLoop s (AC6 P σ) := by
  have hs := h.hs
  have ok := hs.1.ok
  have hpl := hs.1.pl1021
  have hp8 := hs.1.pl8
  have fit := hs.1.fit
  have hb := hs.1.bufA
  have hF : oBuf + P.pl ≤ P.lay.F := by show _ ≤ frameBytes; simp only [oBuf, frameBytes]; omega
  have hpt : (P.B + BitVec.ofNat 32 oBuf).toNat + P.pl ≤ 2 ^ 32 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := oBuf) (by decide)]
    simp only [oBuf, frameBytes] at fit ⊢
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  refine WP.mono (zero_ok (p := P.B + BitVec.ofNat 32 oBuf) (n := P.pl) (by omega) (by omega)
    hpt h.si h.cx h.ax (by rw [hb]; exact hs.2.inFr hF)) fun t ht => ?_
  have fr : Frame [⟨P.lay.fr oBuf, P.pl⟩] s.mem t.mem := by
    rw [ht.mem, hb]
    have := Proof.RsaPkcs1Sig.frame_writeBytes s.mem (P.lay.fr oBuf) (List.replicate P.pl 0)
    simpa using this
  have st : P.lay.St σ t := hs.2.frameW hF fr ht.rd ht.wr (ht.other _ (by decide) (by decide))
  have hd : oBuf + P.pl ≤ P.lay.F + 16 := by show _ ≤ frameBytes + 16; simp only [oBuf, frameBytes]; omega
  obtain ⟨r₀, cr, bx⟩ := h.cr
  have hbo : Spec.Rsa.bytesAt t.mem (P.out.setWidth 64) P.K = Spec.Rsa.bytesAt s.mem (P.out.setWidth 64) P.K :=
    Proof.RsaPkcs1Sig.bytesAt_frame fr (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (ok.stk_fr (R := P.OUT) (.inr (by simp)) hd).symm) (by have := hs.1.k1024; omega)
  refine ⟨⟨hs.1, st⟩, h.full, TapeW.frame hs h.tape fr fun r hr => ?_,
    ⟨r₀, fun hp => written_congr hbo (cr hp), by rw [ht.other _ (by decide) (by decide), bx]⟩⟩
  simp only [List.mem_singleton] at hr; subst hr
  exact (ok.stk_fr (R := P.TAPE) (.inr (by simp)) hd).symm

theorem wipe_vp : VP (AC5 P) zeroLoop (AC6 P) :=
  VP.taint [.esi, .ecx] zeroLoop_taint (fun _ _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h₁.si, h₂.si]
      · rw [h₁.cx, h₂.cx]) fun _ _ h => wipe_wp h

/-! ## The result -/

theorem writtenRandom_of {m : Mem} {a : Addr} {K : Nat} {r₀ : BitVec 32} {o : Option (List Byte)}
    (h : Spec.Rsa.written m a K r₀ o) : Spec.RsaPkcs1Enc.writtenRandom m a K (2 - r₀) o := by
  cases o with
  | some y => obtain ⟨rfl, hb⟩ := h; exact ⟨by decide, hb⟩
  | none => obtain ⟨rfl, hb⟩ := h; exact ⟨by decide, hb⟩

theorem AC6.res {σ s : State} (h : AC6 P σ s) : Res P σ s.mem (s.gpr .ebx) := by
  have hs := h.hs
  obtain ⟨r₀, cr, bx⟩ := h.cr
  have hpre : Spec.RsaPkcs1Enc.nonzeroPrefix P.pl (rB P σ) = some (psv P σ, P.mask.length) := by
    have := prefix_full (n := P.pl) (R := rB P σ) (by rw [hs.1.scanN, hs.1.cntE (Nat.le_refl _), h.full])
    rwa [hs.1.scanN] at this
  obtain ⟨ho, hu⟩ := padSearch_accepted hpre
  unfold Res
  rw [ho, hu, bx]
  refine ⟨⟨0, h.tape, ?_⟩, fun hp => writtenRandom_of (cr hp)⟩
  simp only [Spec.Entropy.Result.Requests, ho]

theorem final_vp : VP (AC6 P) (.block [.mov .eax (.reg .ebx)]) (Fin P) :=
  VP.taint [.esp] ret_taint (sp_agree fun _ _ h => h.hs) fun _ _ h =>
    wp_mov fun t u => WP.block_nil ⟨⟨h.hs.1, h.hs.2.upd u (by decide)⟩, by rw [u.mem, u.gpr]; exact h.res⟩

theorem accept_vp (encName : String) (c : Ver.PublicImpl) :
    VP (fun σ s => Dz P σ s ∧ isa.eval .e s = some true)
      (accept encName (Impl.RsaPkcs1Enc.X86.Precomputed.code c.name c.code)) (Fin P) :=
  tapePtr_vp.seq (tapeAcc_vp.seq (callArgs_vp.seq ((call_vp encName c).seq (status_vp.seq (wipe_vp.seq final_vp)))))

end VG.Proof.RsaPkcs1Enc.X86.Rnd
