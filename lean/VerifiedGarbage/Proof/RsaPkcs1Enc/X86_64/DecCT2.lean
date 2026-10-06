import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.DecCT1

/-!
# RSAES-PKCS1-v1_5 decryption on x86-64: constant time, `DH` and `KDK`

Each block addresses only the frame (from `rsp`), and each call's public
arguments are functions of the public data.
-/

namespace VG.Proof.RsaPkcs1Enc.X86_64.Dec

open VG VG.X86_64 VG.Impl.RsaPkcs1Enc.X86_64.Decrypt
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.RsaPkcs1Enc.X86_64
open VG.Proof.Sha256.X86_64 (Compress)

variable {v : Compress}

/-- A block from a state with `Cx` and facts `F`. -/
theorem cx_blk {F F' : State → State → Prop} {is : List Instr}
    {hc : VG.Taint.Hint VG.X86_64.Taint.T} (h : (taint.check (Taint.ofRegs [.rsp]) (.block is) hc).isSome = true)
    (hw : ∀ s t R EM, DPre s → Ctx s R EM t → F s t → WP isa (.block is) t fun t' => Ctx s R EM t' ∧ F' s t') :
    RelCT isa (Two (At fun s t => Cx s t ∧ F s t)) (.block is) (Two (At fun s t => Cx s t ∧ F' s t)) :=
  two_blk [.rsp] (rsp_pin fun _ _ h => h.1) h fun s t hp ⟨⟨R, EM, hc⟩, f⟩ =>
    WP.mono (hw s t R EM hp hc f) fun _ ⟨hc', f'⟩ => ⟨⟨R, EM, hc'⟩, f'⟩

/-- A call from a state with `Cx` and facts `F`, which keeps `Ctx`. -/
theorem cx_call {F : State → State → Prop} {c : Prog isa}
    (hct : RelCT isa (Two (At fun s t => Cx s t ∧ F s t)) c fun _ _ => True)
    (hw : ∀ s t R EM, DPre s → Ctx s R EM t → F s t → WP isa c t fun t' => Ctx s R EM t' ∧ FrmKeep s t.mem t'.mem) :
    RelCT isa (Two (At fun s t => Cx s t ∧ F s t)) c (Two (At fun s t => Cx s t ∧ True)) :=
  two_then hct fun s t hp ⟨⟨R, EM, hc⟩, f⟩ => WP.mono (hw s t R EM hp hc f) fun _ h => ⟨⟨R, EM, h.1⟩, trivial⟩

theorem hashD_ct : RelCT isa (Two (At fun s t => Cx s t ∧ True)) (hashD (HH v)) fun _ _ => True := by
  refine RelCT.seq (cx_blk (F' := fun s t => t.gpr .rdi = scA s 0) (by taint_decide)
    fun s t R EM hp hc _ => WP.mono (shaInitArgs_run hp hc) fun _ ⟨hc', _, h⟩ => ⟨hc', h⟩) ?_
  refine RelCT.seq (cx_call (init_two fun _ _ h => h) fun s t R EM hp hc h => init_cx hp hc h) ?_
  refine RelCT.seq (cx_blk (F' := fun s t => t.gpr .rdi = scA s 0 ∧ t.gpr .rsi = BitVec.ofNat 64 0 ∧
      t.gpr .rdx = scA s sD ∧ (t.gpr .rcx).toNat = kOf s ∧ t.gpr .r8 = scA s sWork) (by taint_decide)
    fun s t R EM hp hc _ => WP.mono (shaUpdArgs_run hp hc) fun _ ⟨hc', _, h1, h2, h3, h4, h5⟩ =>
      ⟨hc', h1, h2, h3, by rw [h4], h5⟩) ?_
  refine RelCT.seq (cx_call (upd_two (da := fun s => scA s sD) (L := kOf) (si := fun _ => BitVec.ofNat 64 0)
      (fun _ _ h => h) (fun s hp => DataOk.scr hp (by decide) (by have := hp.k2; unfold sD scrBytes kOf; omega))
      (scA_pin sD) (fun _ _ S => S.k) (fun _ _ _ => rfl))
    fun s t R EM hp hc ⟨h1, _, h3, h4, h5⟩ =>
      upd_cx hp hc (DataOk.scr hp (by decide) (by have := hp.k2; unfold sD scrBytes kOf; omega)) h1 h3 h4 h5) ?_
  refine RelCT.seq (cx_blk (F' := fun s t => t.gpr .rdi = scA s 0 ∧ t.gpr .rsi = s.gpr .r8 ∧
      t.gpr .rdx = scA s sDH ∧ t.gpr .rcx = scA s sWork) (by taint_decide)
    fun s t R EM hp hc _ => WP.mono (shaFinArgs_run hp hc) fun _ ⟨hc', _, h⟩ => ⟨hc', h⟩) ?_
  exact fin_two fun _ _ h => ⟨h.1, h.2⟩


/-- The arguments of HMAC's `init` with the key at `scratch + kOff`. -/
def HIA (kOff : Nat) (s t : State) : Prop :=
  t.gpr .rdi = scA s 0 ∧ t.gpr .rsi = scA s sOuter ∧ t.gpr .rdx = scA s kOff ∧ t.gpr .rcx = BitVec.ofNat 64 32 ∧
    t.gpr .r8 = scA s sWork

theorem macInit_ct {F : State → State → Prop} {kOff : Nat} (hk1 : sMsg ≤ kOff) (hk2 : kOff + 32 ≤ scrBytes)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (h : (taint.check (Taint.ofRegs [.rsp]) (.block (macInitArgs kOff)) hc).isSome = true) :
    RelCT isa (Two (At fun s t => Cx s t ∧ F s t)) (.seq (.block (macInitArgs kOff))
      (.call (HH v).hmacInitN (HH v).hmacInit)) (Two (At fun s t => Cx s t ∧ True)) := by
  refine RelCT.seq (cx_blk (F' := HIA kOff) h fun s t R EM hp hc _ =>
    WP.mono (macInitArgs_run hp hc (by unfold scrBytes at hk2; omega)) fun _ ⟨hc', _, h⟩ => ⟨hc', h⟩) ?_
  exact cx_call (hinit_two hk1 hk2 fun _ _ h => h) fun s t R EM hp hc ⟨h1, h2, h3, h4, h5⟩ =>
    hinit_cx hp hc hk1 hk2 h1 h2 h3 h4 h5

theorem kdkMac_ct : RelCT isa (Two (At fun s t => Cx s t ∧ True)) (kdkMac (HH v)) fun _ _ => True := by
  refine RelCT.assoc ((macInit_ct (v := v) (kOff := sDH) (by decide) (by decide) (by taint_decide)).seq ?_)
  refine RelCT.seq (cx_blk (F' := fun s t => t.gpr .rdi = scA s 0 ∧ t.gpr .rsi = BitVec.ofNat 64 64 ∧
      t.gpr .rdx = stackArg s 3 ∧ (t.gpr .rcx).toNat = kOf s ∧ t.gpr .r8 = scA s sWork) (by taint_decide)
    fun s t R EM hp hc _ => WP.mono (kdkUpdArgs_run hp hc) fun _ ⟨hc', _, h⟩ => ⟨hc', h⟩) ?_
  refine RelCT.seq (cx_call (upd_two (da := fun s => stackArg s 3) (L := kOf) (si := fun _ => BitVec.ofNat 64 64)
      (fun _ _ h => h) (fun s hp => DataOk.c hp) (arg_pin (by decide)) (fun _ _ S => S.k) (fun _ _ _ => rfl))
    fun s t R EM hp hc ⟨h1, _, h3, h4, h5⟩ => upd_cx hp hc (DataOk.c hp) h1 h3 h4 h5) ?_
  refine RelCT.seq (cx_blk (F' := fun s t => t.gpr .rdi = scA s 0 ∧ t.gpr .rsi = scA s sOuter ∧
      t.gpr .rdx = BitVec.ofNat 64 (64 + kOf s) ∧ t.gpr .rcx = scA s sKDK ∧ t.gpr .r8 = scA s sWork)
      (by taint_decide)
    fun s t R EM hp hc _ => WP.mono (kdkFinArgs_run hp hc) fun _ ⟨hc', _, h⟩ => ⟨hc', h⟩) ?_
  exact hfin_two (dOff := fun _ => sKDK) (cnt := fun s => BitVec.ofNat 64 (64 + kOf s)) (fun _ => by decide)
    (fun _ => by decide) (fun _ _ h => h) (fun _ _ _ => rfl) (fun _ _ S => by simp only [S.k])

end VG.Proof.RsaPkcs1Enc.X86_64.Dec
