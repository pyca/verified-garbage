module

import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.DecCorrect
import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.Alloc
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.DecCT2
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.DecCorrect
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.Alloc
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.DecCT2
meta import VerifiedGarbage.Proof.Framework.TaintBatch
public import VerifiedGarbage.Proof.Framework.X86_64.Scrub
import VerifiedGarbage.Proof.Rsa.X86_64.PrivImpl
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.DecResult
import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.DecCT3
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.DecResult
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.DecCT3
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT

/-! ### `RsaPkcs1Enc.X86_64.DecCT4`, which only this module used -/

section

/-! ### `RsaPkcs1Enc.X86_64.DecCT1`, which only this module used -/

section

/-!
# RSAES-PKCS1-v1_5 decryption on x86-64: constant time, up to `D`

The first block, the private-key operation (constant time for its
contract, whose public data agree), and `D = I2OSP(d, k)`, whose loops
address `scratch` and `d` from pointers and lengths that are public.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.X86_64.Dec

open VG VG.X86_64 VG.Impl.RsaPkcs1Enc.X86_64.Decrypt
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.RsaPkcs1Enc.X86_64

variable {X : State → State → Prop}

/-- Callee-saved registers but `rsp` as on entry. -/
def CS (s t : State) : Prop := ∀ r ∈ calleeSaved, r ≠ .rsp → t.gpr r = s.gpr r

def J0 (s t : State) : Prop := t = allocState frameBytes s
def JP (s t : State) : Prop := PostPriv s t ∧ CS s t

/-- A buffer the function only reads, as a callee from the frame sees it. -/
theorem entryBytes {s t : State} (hp : DPre s) (h : CallAt s t) (rd wr : List Region) {p : Addr} {len : Nat}
    (hk : (stkR s).Disjoint ⟨p, len⟩) (ho : (outR s).Disjoint ⟨p, len⟩) (hm : (mlR s).Disjoint ⟨p, len⟩)
    (hs : (⟨p, len⟩ : Region).Disjoint (scrR s)) (hl : len ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt (t.callEntry.withRegions rd wr).mem p len = Spec.Rsa.bytesAt s.mem p len := by
  have hk2 := hp.k2
  rw [State.withRegions_mem]
  exact bytes_of_frame (frame_call (frame_of_outside h.out) (callEntry_frame h.rsp) fun r hr => by
    rw [List.mem_singleton.mp hr]; exact ⟨stkR s, List.mem_cons_self .., below_sub s (by decide)⟩) hk ho hm hs.symm hl

/-- What the private-key operation's contract makes public, from the entry state. -/
theorem priv_view {a s t : State} {rds : List Region} (S : Sib X a s) (h : CallAt s t) :
    [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp].map (t.callEntry.withRegions rds (privWr s)).gpr =
      [a.gpr .rdi, a.gpr .r8, a.gpr .rcx, a.gpr .r8, a.gpr .r9, stackArg a 0, fb a - 8] ∧
    (List.range 14).map (stackArg (t.callEntry.withRegions rds (privWr s))) =
      ((List.range 14).map fun i => stackArg a (i + 3)) ∧
    Spec.Rsa.bytesAt (t.callEntry.withRegions rds (privWr s)).mem
      ((t.callEntry.withRegions rds (privWr s)).gpr .rdx)
      ((t.callEntry.withRegions rds (privWr s)).gpr .rcx).toNat = nB a ∧
    Spec.Rsa.bytesAt (t.callEntry.withRegions rds (privWr s)).mem
      ((t.callEntry.withRegions rds (privWr s)).gpr .r8)
      ((t.callEntry.withRegions rds (privWr s)).gpr .r9).toNat = eB a := by
  have hp := S.p
  have hk2 := hp.k2
  have hsi := hp.hsi
  have g : ∀ {r : Reg}, r ≠ .rsp → (t.callEntry.withRegions rds (privWr s)).gpr r = t.gpr r := fun hr => by
    rw [State.withRegions_gpr, State.callEntry_gpr _ hr]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [List.map_cons, List.map_nil]
    rw [g (by decide), h.rdi, S.gpr (by decide), g (by decide), h.rsi, S.gpr (by decide), g (by decide), h.rdx,
      S.gpr (by decide), g (by decide), h.rcx, g (by decide), h.r8, S.gpr (by decide), g (by decide), h.r9,
      S.arg (by decide), State.withRegions_gpr, State.callEntry_rsp, h.rsp, S.fb, S.gpr (r := .r9) (by decide)]
  · refine List.map_congr_left fun i hi => ?_
    rw [List.mem_range] at hi
    rw [priv_args h _ _ hi, S.arg (by omega_using [hi])]
  · rw [g (by decide), g (by decide), h.rdx, h.rcx, entryBytes hp h _ _ hp.dKn
      (by have := hp.dOn; rw [outR]; exact this) hp.dMn hp.dns (by have := hp.wN; omega_using [])]
    exact S.n
  · rw [g (by decide), g (by decide), h.r8, h.r9, entryBytes hp h _ _ hp.dKe
      (by have := hp.dOe; rw [outR]; exact this) hp.dMe hp.des (by have := hp.wE; omega_using [])]
    exact S.e

/-! ## `D` -/

def J1 (s t : State) : Prop := ∃ R EM, P1 s R EM t
def J2 (s t : State) : Prop := ∃ R EM t₀, P1 s R EM t₀ ∧ ZInv s t₀ (kOf s) t
def J3 (s t : State) : Prop := ∃ R EM t₀, P2 s R EM t₀ t
def JDB (s t : State) : Prop := ∃ R EM, DB s R EM t

theorem dBuild_ct : RelCT isa (Two (At X JP)) dBuild fun _ _ => True := by
  refine RelCT.seq (two_blk (J' := J1) [.rsp] (pins (J := JP) [(.rsp, fb)] (by
      simp only [List.mem_singleton]; rintro p rfl s t h; exact h.1.rsp)
    (by simp only [List.mem_singleton]; rintro p rfl; exact fb_pin)) (by taint_decide)
    fun s t hp ⟨h, hcs⟩ => WP.mono (p1_step hp h hcs) fun _ h' => ⟨_, _, h'⟩) ?_
  refine RelCT.seq (two_blk (J' := J2) [.rsp, .rdi, .rcx, .r10] (pins (J := J1) [(.rsp, fb), (.rdi, sc),
      (.rcx, fun s => s.gpr .r8), (.r10, fun _ => BitVec.ofNat 64 0)] (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro p (rfl | rfl | rfl | rfl) s t ⟨_, _, h⟩
        · exact h.ctx.rsp
        · exact h.rdi
        · exact h.rcx
        · exact h.r10) (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro p (rfl | rfl | rfl | rfl)
        · exact fb_pin
        · exact sc_pin
        · exact gpr_pin (by decide)
        · exact const_pin _)) (by taint_decide)
    fun s t hp ⟨_, _, h⟩ => WP.mono (zeroLoop_ok hp h) fun _ h' => ⟨_, _, _, h, h'⟩) ?_
  refine RelCT.seq (two_blk (J' := J3) [.rsp] (pins (J := J2) [(.rsp, fb)] (by
      simp only [List.mem_singleton]; rintro p rfl s t ⟨_, _, _, h₀, h⟩
      exact (h.keep.gpr (by decide)).trans h₀.ctx.rsp)
    (by simp only [List.mem_singleton]; rintro p rfl; exact fb_pin)) (by taint_decide)
    fun s t hp ⟨_, _, _, h₀, h⟩ => WP.mono (p2_step hp h₀ h) fun _ h' => ⟨_, _, _, h'⟩) ?_
  exact two_taint [.rsp, .rsi, .rcx, .rdi, .r10] (pins (J := J3) [(.rsp, fb), (.rsi, fun s => stackArg s 1),
      (.rcx, fun s => stackArg s 2), (.rdi, fun s => off (sc s) (kOf s - dlOf s)),
      (.r10, fun _ => BitVec.ofNat 64 0)] (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro p (rfl | rfl | rfl | rfl | rfl) s t ⟨_, _, _, h⟩
        · exact h.ctx.rsp
        · exact h.rsi
        · exact h.rcx
        · exact h.rdi
        · exact h.r10) (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro p (rfl | rfl | rfl | rfl | rfl)
        · exact fb_pin
        · exact arg_pin (by decide)
        · exact arg_pin (by decide)
        · intro a s S; dsimp only; rw [S.scr, S.k, show dlOf s = dlOf a by simp only [dlOf, S.arg (i := 2) (by decide)]]
        · exact const_pin _)) (by taint_decide)

theorem dBuild_two : RelCT isa (Two (At X JP)) dBuild (Two (At X JDB)) :=
  two_then dBuild_ct fun _ _ hp ⟨h, hcs⟩ => WP.mono (dBuild_step hp h hcs) fun _ h' => ⟨_, _, h'⟩

end VG.Proof.RsaPkcs1Enc.X86_64.Dec

end

end

/-!
# RSAES-PKCS1-v1_5 decryption on x86-64: constant time, from `KDK` on

IRPRF's loops (`prfLoop_ct`), the mask, `AL`, the scan and the output: each
loop's addresses and branches are functions of the pointers and `k`, from
the registers its first block sets; `AL`, the scan's results, the validity
mask and the selected length are never among them.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.X86_64.Dec

open VG VG.X86_64 VG.Impl.RsaPkcs1Enc.X86_64.Decrypt
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.RsaPkcs1Enc.X86_64
open VG.Proof.Sha256.X86_64 (Compress)

variable {X : State → State → Prop}

variable {v : Compress}

def JHD (s t : State) : Prop := ∃ R EM, HD s R EM t
def JKD (s t : State) : Prop := ∃ R EM, KD s R EM t
def JCL (s t : State) : Prop := ∃ R EM, CLd s R EM t
def JAM (s t : State) : Prop := ∃ R EM, AMd s R EM t
def JMK (s t : State) : Prop := ∃ R EM, MK s R EM t
def JAL (s t : State) : Prop := ∃ R EM, AL s R EM t
def JSC (s t : State) : Prop := ∃ R EM, SC s R EM t

/-! ## `DH` and `KDK` -/

theorem hashD_two : RelCT isa (Two (At X JDB)) (hashD (HH v)) (Two (At X JHD)) :=
  two_then (two_weak (fun _ _ ⟨R, EM, h⟩ => ⟨⟨R, EM, h.ctx⟩, trivial⟩) hashD_ct)
    fun _ _ hp ⟨_, _, h⟩ => WP.mono (hashD_step hp h) fun _ h' => ⟨_, _, h'⟩

theorem kdkMac_two : RelCT isa (Two (At X JHD)) (kdkMac (HH v)) (Two (At X JKD)) :=
  two_then (two_weak (fun _ _ ⟨R, EM, h⟩ => ⟨⟨R, EM, h.ctx⟩, trivial⟩) kdkMac_ct)
    fun _ _ hp ⟨_, _, h⟩ => WP.mono (kdkMac_step hp h) fun _ h' => ⟨_, _, h'⟩

/-! ## `CL` and `AM` -/

theorem clLoop_ct : RelCT isa (Two (At X fun s t => Cx s t ∧ True)) (clLoop (HH v)) fun _ _ => True := by
  refine RelCT.seq (two_blk (J' := fun s t => Cx s t ∧ GW (fun _ => 8) 0 s t.mem ∧ True) [.rsp]
    (rsp_pin fun _ _ h => h.1) (by taint_decide) fun s t hp ⟨⟨R, EM, hc⟩, _⟩ =>
      WP.mono (clInit_run hp hc) fun _ ⟨hc', hI, hNB, _⟩ => ⟨⟨R, EM, hc'⟩, ⟨Nat.succ_pos 7, hI, hNB⟩, trivial⟩) ?_
  exact prfLoop_ct (v := v) (fun _ _ _ => rfl) (by decide) (by decide) (fun _ _ => by decide)
    (fun s hp R EM t i hc hi hdi hax _ => WP.mono (msgCL_run hp hc (by omega_using [hi]) hdi hax) fun _ h => ⟨h.1, h.2.2⟩)
    (fun s hp R EM t i hc hi hI _ => incr8_ok hp hc hi hI) (by taint_decide) (by taint_decide) (by taint_decide)
    (by taint_decide)

theorem clLoop_two : RelCT isa (Two (At X JKD)) (clLoop (HH v)) (Two (At X JCL)) :=
  two_then (two_weak (fun _ _ ⟨R, EM, h⟩ => ⟨⟨R, EM, h.ctx⟩, trivial⟩) clLoop_ct)
    fun _ _ hp ⟨_, _, h⟩ => WP.mono (clLoop_step hp h) fun _ h' => ⟨_, _, h'⟩

theorem nb_le {s : State} (hp : DPre s) : 0 < nbOf s ∧ nbOf s ≤ 32 := by
  have hk1 := hp.k1
  have hk2 := hp.k2
  have hkk : kOf s ≤ 1024 := hk2
  have hk64 : 64 ≤ kOf s := hk1
  unfold nbOf; omega_using [hkk, hk64]

theorem amLoop_ct : RelCT isa (Two (At X JCL)) (amLoop (HH v)) fun _ _ => True := by
  refine RelCT.seq (two_blk (J' := fun s t => Cx s t ∧ GW nbOf 0 s t.mem ∧ True) [.rsp]
    (rsp_pin fun _ _ ⟨R, EM, h⟩ => ⟨R, EM, h.ctx⟩) (by taint_decide) fun s t hp ⟨R, EM, h⟩ =>
      WP.mono (amInit_run hp h.ctx) fun _ ⟨hc', hI, hNB, _⟩ =>
        ⟨⟨R, EM, hc'⟩, ⟨(nb_le hp).1, hI, hNB.trans h.sNB⟩, trivial⟩) ?_
  exact prfLoop_ct (v := v) (N := nbOf) (fun _ _ S => by simp only [nbOf, S.k]) (by decide) (by decide)
    (fun s hp => by have := nb_le hp; unfold sAM scrBytes; omega_using [this])
    (fun s hp R EM t i hc hi hdi hax h9 => WP.mono (msgAM_run hp hc (by have := nb_le hp; omega_using [hi, this]) hdi hax h9)
      fun _ h => ⟨h.1, h.2.2⟩)
    (fun s hp R EM t i hc hi hI hNB => incrNB_ok hp hc hi hI hNB) (by taint_decide) (by taint_decide)
    (by taint_decide) (by taint_decide)

theorem amLoop_two : RelCT isa (Two (At X JCL)) (amLoop (HH v)) (Two (At X JAM)) :=
  two_then amLoop_ct fun _ _ hp ⟨_, _, h⟩ => WP.mono (amLoop_step hp h) fun _ h' => ⟨_, _, h'⟩

/-! ## The mask, `AL` and the scan -/

theorem maskPart_ct : RelCT isa (Two (At X JAM)) maskPart fun _ _ => True := by
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

theorem maskPart_two : RelCT isa (Two (At X JAM)) maskPart (Two (At X JMK)) :=
  two_then maskPart_ct fun _ _ hp ⟨_, _, h⟩ => WP.mono (maskPart_step hp h) fun _ h' => ⟨_, _, h'⟩

theorem alInit_run {s : State} (hp : DPre s) {R : BitVec 64} {EM : List Byte} {t : State} (hc : Ctx s R EM t) :
    WP isa (.block alInit) t fun t' => t'.gpr .rsi = scA s sCL ∧ t'.gpr .rcx = BitVec.ofNat 64 0 := by
  have hs := hc.frm hp
  xrun [alInit, scr, List.cons_append, List.nil_append, ea_sp, hc.rsp, hs.ld (d := oScr) (by decide),
    hc.slots.sScr, sx (d := sCL) (by decide)]

theorem alPart_ct : RelCT isa (Two (At X JMK)) alPart fun _ _ => True := by
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

theorem alPart_two : RelCT isa (Two (At X JMK)) alPart (Two (At X JAL)) :=
  two_then alPart_ct fun _ _ hp ⟨_, _, h⟩ => WP.mono (alPart_step hp h) fun _ h' => ⟨_, _, h'⟩

theorem scanInit_run {s : State} (hp : DPre s) {R : BitVec 64} {EM : List Byte} {t : State} (hc : Ctx s R EM t) :
    WP isa (.block scanInit) t fun t' => t'.gpr .rdi = s.gpr .rdi ∧ t'.gpr .r9 = BitVec.ofNat 64 (kOf s) ∧
      t'.gpr .rcx = BitVec.ofNat 64 2 := by
  have hs := hc.frm hp
  have h8 : s.gpr .r8 = BitVec.ofNat 64 (kOf s) := by simp [kOf]
  xrun [scanInit, ea_sp, hc.rsp, hs.ld (d := oOut) (by decide), hs.ld (d := oK) (by decide), hc.slots.sOut,
    hc.slots.sK, h8]

theorem scanPart_ct : RelCT isa (Two (At X JAL)) scanPart fun _ _ => True := by
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

theorem scanPart_two : RelCT isa (Two (At X JAL)) scanPart (Two (At X JSC)) :=
  two_then scanPart_ct fun _ _ hp ⟨_, _, h⟩ => WP.mono (scanPart_step hp h) fun _ h' => ⟨_, _, h'⟩

end VG.Proof.RsaPkcs1Enc.X86_64.Dec

end

end

/-!
# RSAES-PKCS1-v1_5 decryption on x86-64: constant time

The output: the validity mask, the selected length and the mask of the
private-key operation's result are computed without branches from `EM`'s
first bytes, the scan and the result's slot; `msg_len`'s store and the
selection's loads and stores are at addresses from the pointers alone, and
the loop runs `k` times. With the earlier phases, `dec_constantTime`, and
`dec_verified`.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.X86_64.Dec

open VG VG.X86_64 VG.Impl.RsaPkcs1Enc.X86_64.Decrypt
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.RsaPkcs1Enc.X86_64
open VG.Proof.Sha256.X86_64 (Compress)

variable {X : State → State → Prop}

variable {v : Compress}

/-- After the checks: `EM` in `rdi` and `k` in `r9`. -/
def JV (s t : State) : Prop := Cx s t ∧ t.gpr .rdi = s.gpr .rdi ∧ t.gpr .r9 = BitVec.ofNat 64 (kOf s)

theorem valid_step {s : State} (hp : DPre s) {R : BitVec 64} {EM : List Byte} {t : State} (h : SC s R EM t) :
    WP isa (.block validBlock) t (JV s) := by
  have hk1 := hp.k1
  have hk2 := hp.k2
  have hkk : kOf s ≤ 1024 := hk2
  have hkk1 : 64 ≤ kOf s := hk1
  have hc := h.ctx
  have hs := hc.frm hp
  have hsep : (firstZero EM (kOf s)).getD 0 < kOf s := by
    cases hf : firstZero EM (kOf s) with
    | none => simp; omega_using [hkk1]
    | some i => have := firstZero_some hf; simpa using this.2.1
  have hR : t.mem.readW (fb s + BitVec.ofNat 64 oR) 64 = R := hc.sR
  have hio : ∀ i n, i + n ≤ kOf s → InRegions (t.rd ++ t.wr) (off (s.gpr .rdi) i) n := fun i n h' =>
    let ⟨r, hr, hcr⟩ := hc.outIn hp h'; ⟨r, List.mem_append_right _ hr, hcr⟩
  exact WP.mono (validBlock_run (p := s.gpr .rdi) (F := fb s) (b0 := EM.getD 0 1) (b1 := EM.getD 1 1)
    h.rdi (by rw [← hc.em (i := 0) (by omega_using [hkk1])]; exact (congrArg t.mem (off_zero _)).symm)
    (hc.em (by omega_using [hkk1])) (by have := hio 0 1 (by omega_using [hkk1]); rwa [off_zero] at this) (hio 1 1 (by omega_using [hkk1])) h.rdx h.r10 h.r11
    h.r9 hc.rsp hR (hs.ld (d := oR) (by decide)) hsep (by omega_using [hkk]))
    fun _ ⟨⟨hm₁, _⟩, k₁⟩ => ⟨⟨R, EM, hc.regs hp hm₁ k₁ (by decide)⟩, (k₁.gpr (by decide)).trans h.rdi,
      (k₁.gpr (by decide)).trans h.r9⟩

/-- After `outPtrs`: `msg_len` in `r8` and `AM` in `rcx`. -/
def JO (s t : State) : Prop :=
  Cx s t ∧ (t.gpr .rdi = s.gpr .rdi ∧ t.gpr .r9 = BitVec.ofNat 64 (kOf s) ∧ t.gpr .r8 = s.gpr .rdx ∧
    t.gpr .rcx = scA s sAM)

theorem outPtrs_run {s : State} (hp : DPre s) {R : BitVec 64} {EM : List Byte} {t : State} (hc : Ctx s R EM t) :
    WP isa (.block outPtrs) t fun t' => Ctx s R EM t' ∧ t'.mem = t.mem ∧ t'.gpr .rdi = t.gpr .rdi ∧
      t'.gpr .r9 = t.gpr .r9 ∧ t'.gpr .r8 = s.gpr .rdx ∧ t'.gpr .rcx = scA s sAM := by
  have hs := hc.frm hp
  refine (WP.keep [.r8, .rcx] (c := .block outPtrs) (Q := fun t' => t'.mem = t.mem ∧
    t'.gpr .r8 = s.gpr .rdx ∧ t'.gpr .rcx = scA s sAM) ?_ rfl).mono
    fun t' ⟨h, k⟩ => ⟨hc.regs hp h.1 k (by decide), h.1, k.gpr (by decide), k.gpr (by decide), h.2⟩
  xrun [outPtrs, scr, List.cons_append, List.nil_append, ea_sp, hc.rsp, hs.ld (d := oML) (by decide),
    hs.ld (d := oScr) (by decide), hc.slots.sML, hc.slots.sScr, sx (d := sAM) (by decide)]

/-- After `outInit`: the selection's pointers, index and count. -/
def JI (s t : State) : Prop :=
  t.gpr .rdi = s.gpr .rdi ∧ t.gpr .rsi = scA s sAM ∧ t.gpr .rcx = BitVec.ofNat 64 0 ∧
    t.gpr .r9 = BitVec.ofNat 64 (kOf s) ∧ t.gpr .rsp = fb s

theorem outInit_run {s : State} (hp : DPre s) {R : BitVec 64} {EM : List Byte} {t : State} (hc : Ctx s R EM t)
    (h8 : t.gpr .r8 = s.gpr .rdx) (hcx : t.gpr .rcx = scA s sAM) :
    WP isa (.block outInit) t fun t' => t'.gpr .rdi = t.gpr .rdi ∧ t'.gpr .r9 = t.gpr .r9 ∧
      t'.gpr .rsp = t.gpr .rsp ∧ t'.gpr .rsi = scA s sAM ∧ t'.gpr .rcx = BitVec.ofNat 64 0 := by
  have hml : InRegions t.wr (s.gpr .rdx) 8 :=
    ⟨mlR s, by rw [hc.wr, hp.hwr]; simp [mlR], Region.contains_self _ _⟩
  refine (WP.keep [.rdx, .rsi, .rcx] (c := .block outInit) (Q := fun t' =>
    t'.gpr .rsi = scA s sAM ∧ t'.gpr .rcx = BitVec.ofNat 64 0) ?_ rfl).mono
    fun t' ⟨h, k⟩ => ⟨k.gpr (by decide), k.gpr (by decide), k.gpr (by decide), h⟩
  xrun [outInit, ea_atd (p := s.gpr .rdx), h8, hml, hcx]

theorem selPart_ct : RelCT isa (Two (At X JSC)) selPart fun _ _ => True := by
  refine RelCT.seq (two_blk (J' := JV) [.rdi, .rsp] (pins (J := JSC) [(.rdi, fun s => s.gpr .rdi), (.rsp, fb)]
    (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro p (rfl | rfl) s t ⟨_, _, h⟩
      · exact h.rdi
      · exact h.ctx.rsp)
    (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro p (rfl | rfl)
      · exact gpr_pin (by decide)
      · exact fb_pin)) (by taint_decide) fun _ _ hp ⟨_, _, h⟩ => valid_step hp h) ?_
  refine RelCT.seq (cx_blk (F := fun s t => t.gpr .rdi = s.gpr .rdi ∧ t.gpr .r9 = BitVec.ofNat 64 (kOf s))
    (F' := fun s t => t.gpr .rdi = s.gpr .rdi ∧ t.gpr .r9 = BitVec.ofNat 64 (kOf s) ∧ t.gpr .r8 = s.gpr .rdx ∧
      t.gpr .rcx = scA s sAM) (by taint_decide)
    fun s t R EM hp hc ⟨hdi, h9⟩ => WP.mono (outPtrs_run hp hc) fun _ ⟨hc', _, hdi', h9', h8', hcx'⟩ =>
      ⟨hc', hdi'.trans hdi, h9'.trans h9, h8', hcx'⟩) ?_
  refine RelCT.seq (two_blk (J' := JI) [.r8, .rcx] (pins (J := JO) [(.r8, fun s => s.gpr .rdx), (.rcx, fun s => scA s sAM)]
    (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro p (rfl | rfl) s t h
      · exact h.2.2.2.1
      · exact h.2.2.2.2)
    (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro p (rfl | rfl)
      · exact gpr_pin (by decide)
      · exact scA_pin _)) (by taint_decide)
    fun s t hp ⟨⟨R, EM, hc⟩, hdi, h9, h8, hcx⟩ => WP.mono (outInit_run hp hc h8 hcx)
      fun _ ⟨hdi', h9', hsp', hsi', hcx'⟩ => ⟨hdi'.trans hdi, hsi', hcx', h9'.trans h9, hsp'.trans hc.rsp⟩) ?_
  exact two_taint [.rdi, .rsi, .rcx, .r9, .rsp] (pins (J := JI) [(.rdi, fun s => s.gpr .rdi),
      (.rsi, fun s => scA s sAM), (.rcx, fun _ => BitVec.ofNat 64 0), (.r9, fun s => BitVec.ofNat 64 (kOf s)),
      (.rsp, fb)]
    (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro p (rfl | rfl | rfl | rfl | rfl) s t h
      · exact h.1
      · exact h.2.1
      · exact h.2.2.1
      · exact h.2.2.2.1
      · exact h.2.2.2.2)
    (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro p (rfl | rfl | rfl | rfl | rfl)
      · exact gpr_pin (by decide)
      · exact scA_pin _
      · exact const_pin _
      · intro a s S; dsimp only; rw [S.k]
      · exact fb_pin)) (by taint_decide)

/-! ## The function -/

/-- The streaming code writes `rsp` only in its callee's frame, for each
implementation's working space. -/
theorem core_stream_sp : ∀ so, Proof.Pbkdf2.Md.X86_64.Sha256.SoOk so →
    (Proof.Pbkdf2.Md.X86_64.Sha256.coreHS so).updC.allInstrs (fun i => !isa.writesSp i) = true ∧
      (Proof.Pbkdf2.Md.X86_64.Sha256.coreHS so).finC.allInstrs (fun i => !isa.writesSp i) = true := by
  intro so h
  rcases h with rfl | rfl | rfl <;> exact ⟨by decide +kernel, by decide +kernel⟩

/-- What follows the private-key operation writes `rsp` only in its callees'
own frames. -/
theorem afterPriv_spSafe (v : Compress) : (afterPriv (HH v)).all (fun i => !isa.writesSp i) = true := by
  have K := Proof.Pbkdf2.Md.X86_64.Sha256.callees v
  have C := Proof.Pbkdf2.Md.X86_64.Sha256.coreOK v
  have hI : (HH v).hmacInit.all (fun i => !isa.writesSp i) = true := Proof.Pbkdf2.Md.X86_64.hmacInit_sp C K
  have hF : (HH v).hmacFin.all (fun i => !isa.writesSp i) = true := Proof.Pbkdf2.Md.X86_64.hmacFin_sp C K
  have hU : (HH v).updC.all (fun i => !isa.writesSp i) = true := Code.all_of_allInstrs
    (Proof.Pbkdf2.Md.X86_64.core_updC K.cSp (core_stream_sp _ v.hso).1)
  have hFi : (HH v).finC.all (fun i => !isa.writesSp i) = true := Code.all_of_allInstrs
    (Proof.Pbkdf2.Md.X86_64.core_finC K.cSp (core_stream_sp _ v.hso).2)
  have hIn : (HH v).initC.all (fun i => !isa.writesSp i) = true := Code.all_of_allInstrs K.iSp
  simp only [afterPriv, dBuild, hashD, kdkMac, clLoop, amLoop, prfBody, maskPart, alPart, scanPart, selPart,
    Code.all, hI, hF, hU, hFi, hIn, Bool.and_true, Bool.true_and]
  decide +kernel

/-! ## Without secret residue

`vg_rsa_pkcs1_decrypt`'s registration scrubs it with `X86_64.Scrub.withScrubAll`,
which clears the registers its code writes and wipes all the stack its
frames and calls use: the residue analysis (`X86_64.RTaint`) does not follow
its code, so nothing of that stack is kept. This is what that needs of the
contract. -/

end VG.Proof.RsaPkcs1Enc.X86_64.Dec
