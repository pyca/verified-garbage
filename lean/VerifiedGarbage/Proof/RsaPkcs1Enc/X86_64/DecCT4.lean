import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.DecCT3
import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.DecSel

/-!
# RSAES-PKCS1-v1_5 decryption on x86-64: constant time, from `KDK` on

IRPRF's loops (`prfLoop_ct`), the mask, `AL`, the scan and the output: each
loop's addresses and branches are functions of the pointers and `k`, from
the registers its first block sets; `AL`, the scan's results, the validity
mask and the selected length are never among them.
-/

namespace VG.Proof.RsaPkcs1Enc.X86_64.Dec

open VG VG.X86_64 VG.Impl.RsaPkcs1Enc.X86_64.Decrypt
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.RsaPkcs1Enc.X86_64
open VG.Proof.Sha256.X86_64 (Compress)

variable {v : Compress}

def JHD (s t : State) : Prop := ∃ R EM, HD s R EM t
def JKD (s t : State) : Prop := ∃ R EM, KD s R EM t
def JCL (s t : State) : Prop := ∃ R EM, CLd s R EM t
def JAM (s t : State) : Prop := ∃ R EM, AMd s R EM t
def JMK (s t : State) : Prop := ∃ R EM, MK s R EM t
def JAL (s t : State) : Prop := ∃ R EM, AL s R EM t
def JSC (s t : State) : Prop := ∃ R EM, SC s R EM t

/-! ## `DH` and `KDK` -/

theorem hashD_two : RelCT isa (Two (At JDB)) (hashD (HH v)) (Two (At JHD)) :=
  two_then (two_weak (fun _ _ ⟨R, EM, h⟩ => ⟨⟨R, EM, h.ctx⟩, trivial⟩) hashD_ct)
    fun _ _ hp ⟨_, _, h⟩ => WP.mono (hashD_step hp h) fun _ h' => ⟨_, _, h'⟩

theorem kdkMac_two : RelCT isa (Two (At JHD)) (kdkMac (HH v)) (Two (At JKD)) :=
  two_then (two_weak (fun _ _ ⟨R, EM, h⟩ => ⟨⟨R, EM, h.ctx⟩, trivial⟩) kdkMac_ct)
    fun _ _ hp ⟨_, _, h⟩ => WP.mono (kdkMac_step hp h) fun _ h' => ⟨_, _, h'⟩

/-! ## `CL` and `AM` -/

theorem clLoop_ct : RelCT isa (Two (At fun s t => Cx s t ∧ True)) (clLoop (HH v)) fun _ _ => True := by
  refine RelCT.seq (two_blk (J' := fun s t => Cx s t ∧ GW (fun _ => 8) 0 s t.mem ∧ True) [.rsp]
    (rsp_pin fun _ _ h => h.1) (by taint_decide) fun s t hp ⟨⟨R, EM, hc⟩, _⟩ =>
      WP.mono (clInit_run hp hc) fun _ ⟨hc', hI, hNB, _⟩ => ⟨⟨R, EM, hc'⟩, ⟨Nat.succ_pos 7, hI, hNB⟩, trivial⟩) ?_
  exact prfLoop_ct (v := v) (fun _ _ _ => rfl) (by decide) (by decide) (fun _ _ => by decide)
    (fun s hp R EM t i hc hi hdi hax _ => WP.mono (msgCL_run hp hc (by omega) hdi hax) fun _ h => ⟨h.1, h.2.2⟩)
    (fun s hp R EM t i hc hi hI _ => incr8_ok hp hc hi hI) (by taint_decide) (by taint_decide) (by taint_decide)
    (by taint_decide)

theorem clLoop_two : RelCT isa (Two (At JKD)) (clLoop (HH v)) (Two (At JCL)) :=
  two_then (two_weak (fun _ _ ⟨R, EM, h⟩ => ⟨⟨R, EM, h.ctx⟩, trivial⟩) clLoop_ct)
    fun _ _ hp ⟨_, _, h⟩ => WP.mono (clLoop_step hp h) fun _ h' => ⟨_, _, h'⟩

theorem nb_le {s : State} (hp : DPre s) : 0 < nbOf s ∧ nbOf s ≤ 32 := by
  have hk1 := hp.k1
  have hk2 := hp.k2
  have hkk : kOf s ≤ 1024 := hk2
  have hk64 : 64 ≤ kOf s := hk1
  unfold nbOf; omega

theorem amLoop_ct : RelCT isa (Two (At JCL)) (amLoop (HH v)) fun _ _ => True := by
  refine RelCT.seq (two_blk (J' := fun s t => Cx s t ∧ GW nbOf 0 s t.mem ∧ True) [.rsp]
    (rsp_pin fun _ _ ⟨R, EM, h⟩ => ⟨R, EM, h.ctx⟩) (by taint_decide) fun s t hp ⟨R, EM, h⟩ =>
      WP.mono (amInit_run hp h.ctx) fun _ ⟨hc', hI, hNB, _⟩ =>
        ⟨⟨R, EM, hc'⟩, ⟨(nb_le hp).1, hI, hNB.trans h.sNB⟩, trivial⟩) ?_
  exact prfLoop_ct (v := v) (N := nbOf) (fun _ _ S => by simp only [nbOf, S.k]) (by decide) (by decide)
    (fun s hp => by have := nb_le hp; unfold sAM scrBytes; omega)
    (fun s hp R EM t i hc hi hdi hax h9 => WP.mono (msgAM_run hp hc (by have := nb_le hp; omega) hdi hax h9)
      fun _ h => ⟨h.1, h.2.2⟩)
    (fun s hp R EM t i hc hi hI hNB => incrNB_ok hp hc hi hI hNB) (by taint_decide) (by taint_decide)
    (by taint_decide) (by taint_decide)

theorem amLoop_two : RelCT isa (Two (At JCL)) (amLoop (HH v)) (Two (At JAM)) :=
  two_then amLoop_ct fun _ _ hp ⟨_, _, h⟩ => WP.mono (amLoop_step hp h) fun _ h' => ⟨_, _, h'⟩

/-! ## The mask, `AL` and the scan -/

theorem maskPart_ct : RelCT isa (Two (At JAM)) maskPart fun _ _ => True := by
  refine RelCT.seq (two_blk (J' := fun s t => t.gpr .r8 = BitVec.ofNat 64 0 ∧
      t.gpr .r9 = BitVec.ofNat 64 (kOf s - 11)) [.rsp]
    (rsp_pin fun _ _ ⟨R, EM, h⟩ => ⟨R, EM, h.ctx⟩) (by taint_decide) fun s t hp ⟨R, EM, h⟩ =>
      WP.mono (maskInit_run hp h.ctx) fun _ ⟨_, h9, h8, _⟩ => ⟨h8, h9⟩) ?_
  exact two_taint [.r8, .r9] (pins [(.r8, fun _ => BitVec.ofNat 64 0), (.r9, fun s => BitVec.ofNat 64 (kOf s - 11))]
    (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro p (rfl | rfl) s t h
      · exact h.1
      · exact h.2)
    (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro p (rfl | rfl)
      · exact const_pin _
      · intro a s S; dsimp only; rw [S.k])) (by taint_decide)

theorem maskPart_two : RelCT isa (Two (At JAM)) maskPart (Two (At JMK)) :=
  two_then maskPart_ct fun _ _ hp ⟨_, _, h⟩ => WP.mono (maskPart_step hp h) fun _ h' => ⟨_, _, h'⟩

theorem alInit_run {s : State} (hp : DPre s) {R : BitVec 64} {EM : List Byte} {t : State} (hc : Ctx s R EM t) :
    WP isa (.block alInit) t fun t' => t'.gpr .rsi = scA s sCL ∧ t'.gpr .rcx = BitVec.ofNat 64 0 := by
  have hs := hc.frm hp
  xrun [alInit, scr, List.cons_append, List.nil_append, ea_sp, hc.rsp, hs.ld (d := oScr) (by decide),
    hc.slots.sScr, sx (d := sCL) (by decide)]

theorem alPart_ct : RelCT isa (Two (At JMK)) alPart fun _ _ => True := by
  refine RelCT.seq (two_blk (J' := fun s t => t.gpr .rsi = scA s sCL ∧ t.gpr .rcx = BitVec.ofNat 64 0) [.rsp]
    (rsp_pin fun _ _ ⟨R, EM, h⟩ => ⟨R, EM, h.am.ctx⟩) (by taint_decide) fun s t hp ⟨R, EM, h⟩ =>
      alInit_run hp h.am.ctx) ?_
  exact two_taint [.rsi, .rcx] (pins [(.rsi, fun s => scA s sCL), (.rcx, fun _ => BitVec.ofNat 64 0)]
    (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro p (rfl | rfl) s t h
      · exact h.1
      · exact h.2)
    (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro p (rfl | rfl)
      · exact scA_pin _
      · exact const_pin _)) (by taint_decide)

theorem alPart_two : RelCT isa (Two (At JMK)) alPart (Two (At JAL)) :=
  two_then alPart_ct fun _ _ hp ⟨_, _, h⟩ => WP.mono (alPart_step hp h) fun _ h' => ⟨_, _, h'⟩

theorem scanInit_run {s : State} (hp : DPre s) {R : BitVec 64} {EM : List Byte} {t : State} (hc : Ctx s R EM t) :
    WP isa (.block scanInit) t fun t' => t'.gpr .rdi = s.gpr .rdi ∧ t'.gpr .r9 = BitVec.ofNat 64 (kOf s) ∧
      t'.gpr .rcx = BitVec.ofNat 64 2 := by
  have hs := hc.frm hp
  have h8 : s.gpr .r8 = BitVec.ofNat 64 (kOf s) := by simp [kOf]
  xrun [scanInit, ea_sp, hc.rsp, hs.ld (d := oOut) (by decide), hs.ld (d := oK) (by decide), hc.slots.sOut,
    hc.slots.sK, h8]

theorem scanPart_ct : RelCT isa (Two (At JAL)) scanPart fun _ _ => True := by
  refine RelCT.seq (two_blk (J' := fun s t => t.gpr .rdi = s.gpr .rdi ∧ t.gpr .r9 = BitVec.ofNat 64 (kOf s) ∧
      t.gpr .rcx = BitVec.ofNat 64 2) [.rsp]
    (rsp_pin fun _ _ ⟨R, EM, h⟩ => ⟨R, EM, h.mkd.am.ctx⟩) (by taint_decide) fun s t hp ⟨R, EM, h⟩ =>
      scanInit_run hp h.mkd.am.ctx) ?_
  exact two_taint [.rdi, .r9, .rcx] (pins [(.rdi, fun s => s.gpr .rdi), (.r9, fun s => BitVec.ofNat 64 (kOf s)),
      (.rcx, fun _ => BitVec.ofNat 64 2)]
    (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro p (rfl | rfl | rfl) s t h
      · exact h.1
      · exact h.2.1
      · exact h.2.2)
    (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro p (rfl | rfl | rfl)
      · exact gpr_pin (by decide)
      · intro a s S; dsimp only; rw [S.k]
      · exact const_pin _)) (by taint_decide)

theorem scanPart_two : RelCT isa (Two (At JAL)) scanPart (Two (At JSC)) :=
  two_then scanPart_ct fun _ _ hp ⟨_, _, h⟩ => WP.mono (scanPart_step hp h) fun _ h' => ⟨_, _, h'⟩

end VG.Proof.RsaPkcs1Enc.X86_64.Dec
