module

import VerifiedGarbage.Proof.RsaPss.X86_64.SignCCall
public import VerifiedGarbage.Proof.RsaPss.X86_64.SignCorrect
import VerifiedGarbage.Proof.RsaPss.SignEncode
import VerifiedGarbage.Proof.RsaPss.SignCases
import VerifiedGarbage.Proof.RsaPss.Params
import VerifiedGarbage.Proof.RsaPss.X86_64.VerifyFrame
import VerifiedGarbage.Proof.RsaPss.X86_64.Safe
import VerifiedGarbage.Proof.Bignum.Octets
import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.RsaPss.X86_64.EncCtx
public import VerifiedGarbage.Proof.RsaPss.X86_64.SignCParams
public import VerifiedGarbage.Proof.RsaPss.X86_64.SignFrame

/-!
# RSASSA-PSS signing on x86-64, around the encoding: correctness

`signC_ok`: from the entry state, `signC` refuses a modulus whose first
byte is zero, computes `emBits`, calls `encode` for the encoding at
`scratch + oEm + lo` after a zero byte, and, if it fits, the private-key
operation on those `k` bytes, which leaves `out` and `rax` as
`RsaPss.sign` says (`sign_encode`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)
open VG.Proof.Rsa.X86_64 (chkContract)

variable {G : Spec.Mgf1.Hash}

/-- `encode`'s return value, tested. -/
theorem test32_ok (u : State) :
    WP isa (.block [.alu32 .test .rax (.reg .rax)]) u fun u' => Keep [.rax] u u' ∧ u'.mem = u.mem ∧
      u'.zf = some (decide ((u.gpr .rax).setWidth 32 = 0)) := by
  refine WP.mono (WP.keep [.rax] (Q := fun u' => u'.mem = u.mem ∧
      u'.zf = some (decide ((u.gpr .rax).setWidth 32 = 0))) ?_ rfl) fun u' ⟨h, k⟩ => ⟨k, h⟩
  xrun []
  rw [BitVec.and_self, Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]

/-- `lo = k - emLen` is 0 or 1. -/
theorem lo_le {k x : Nat} (hx : Nat.log2 x < 8) (hk : 1 ≤ k) : k - Spec.RsaPss.emLength (ebV k x) ≤ 1 := by
  unfold Spec.RsaPss.emLength ebV; omega

/-- The bytes the private-key operation reads: a zero byte (if `lo = 1`),
then the encoding. -/
theorem em_input {m : Mem} {S : Addr} {V : Nat → Byte} {lo el k : Nat} {e : List Byte} (hk : lo + el = k)
    (hlo : lo ≤ 1) (he : Spec.Rsa.bytesAt m (off S (oEm + lo)) el = e) :
    (List.range k).map (fun i => (fun o => if inR [(oEm + lo, el), (oEnc, oRsa - oEnc)] o then m (off S o)
      else upd V oEm 0 o) (oEm + i)) = Spec.RsaPss.zeros lo ++ e := by
  subst he
  have c1 : oEm = 2560 := rfl
  have c3 : oEnc = 4096 := rfl
  apply List.ext_getElem
  · simp [Spec.RsaPss.zeros, Spec.Rsa.bytesAt]; omega
  intro i h1 h2
  simp only [List.length_map, List.length_range] at h1
  simp only [List.getElem_map, List.getElem_range]
  by_cases hi : i < lo
  · rw [ifn (fun ⟨p, hp, a, b⟩ => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl <;> dsimp only at a b <;> omega)]
    rw [List.getElem_append_left (by simp [Spec.RsaPss.zeros]; omega)]
    simp only [upd, Spec.RsaPss.zeros, List.getElem_replicate]
    rw [ifp (by omega)]
  · rw [ifp ⟨_, List.mem_cons_self .., by dsimp only; omega, by dsimp only; omega⟩]
    rw [List.getElem_append_right (by simp [Spec.RsaPss.zeros]; omega)]
    simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range, Spec.RsaPss.zeros, List.length_replicate,
      off_plus]
    congr 2; omega

/-- The slots after `emBitsB` and `encArgs`, from `W`. -/
def encW (W : Nat → BitVec 64) (s : State) (eb : Nat) : Nat → BitVec 64 :=
  upd (upd (upd (upd (upd W 27 (BitVec.ofNat 64 eb)) 28 (BitVec.ofNat 64 (Spec.RsaPss.emLength eb))) 26
    (BitVec.ofNat 64 ((s.gpr .rcx).toNat - Spec.RsaPss.emLength eb))) 0 (off (stackArg s 13) oEnc)) 1
    (stackArg s 14 - BitVec.ofNat 64 (oEnc / 8))

/-- `emBits`, then `encode`'s arguments. -/
theorem encPrep_ok {s u : State} (L : Lay u (fb s) (stackArg s 13)) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem (fb s) (stackArg s 13) V W) (h17 : W 17 = s.gpr .rcx) (h22 : W 22 = stackArg s 14)
    (h37 : W 37 = stackArg s 10) (h39 : W 39 = stackArg s 11) (h40 : W 40 = stackArg s 12)
    (hk1 : 1 ≤ (s.gpr .rcx).toNat)
    (hk2 : (s.gpr .rcx).toNat ≤ 1024) {x : Nat} (hx : x < 256) (h0 : x ≠ 0) (hax : u.gpr .rax = BitVec.ofNat 64 x) :
    WP isa (.block (emBitsB ++ encArgs)) u fun u' => Lay u' (fb s) (stackArg s 13) ∧
      Keep [.rdx, .rax, .r8, .rdi, .rax, .rsi, .rdx, .rcx, .r8, .r9] u u' ∧
      Rep u'.mem (fb s) (stackArg s 13) (upd V oEm 0) (encW W s (ebV (s.gpr .rcx).toNat x)) ∧
      u'.gpr .rdi = off (stackArg s 13) (oEm + ((s.gpr .rcx).toNat - Spec.RsaPss.emLength (ebV (s.gpr .rcx).toNat x))) ∧
      u'.gpr .rsi = BitVec.ofNat 64 (Spec.RsaPss.emLength (ebV (s.gpr .rcx).toNat x)) ∧
      u'.gpr .rdx = stackArg s 10 ∧ u'.gpr .rcx = stackArg s 11 ∧ u'.gpr .r8 = stackArg s 12 ∧
      u'.gpr .r9 = BitVec.ofNat 64 (ebV (s.gpr .rcx).toNat x) := by
  rw [WP.block_append_iff]
  refine WP.mono (emBitsB_ok L R (k := (s.gpr .rcx).toNat) (x := x)
    (by rw [h17, BitVec.ofNat_toNat, BitVec.setWidth_eq]) hk1 hk2 hx h0 hax) fun t ⟨L3, k3, R3⟩ => ?_
  exact WP.mono (encArgs_ok L3 R3 (lo := (s.gpr .rcx).toNat - Spec.RsaPss.emLength (ebV (s.gpr .rcx).toNat x))
    (eb := ebV (s.gpr .rcx).toNat x) (el := Spec.RsaPss.emLength (ebV (s.gpr .rcx).toNat x))
    (dig := stackArg s 10) (q := stackArg s 11) (sl := stackArg s 12) (sw := stackArg s 14)
    (by simp [upd, h22]) (by simp [upd]) (by simp [upd]) (by simp [upd]) (by simp [upd, h37])
    (by simp [upd, h39]) (by simp [upd, h40]))
    fun t' ⟨L4, k4, R4, a, b, c, d, e, f⟩ => ⟨L4, k3.trans k4, R4, a, b, c, d, e, f⟩

theorem signC_ok {encN : String} {encC : Prog isa} {privN : String} {privC : Prog isa}
    (hvE : ∀ s, (encK G).pre s → ∃ t s', Exec isa encC s t s' ∧ abiPreserved s s' ∧ (encK G).post s s')
    (hspE : SpSafe encC) (hdE : encC.x86_64Depth ≤ encStack)
    (hv : ∀ s, chkContract.pre s → ∃ t s', Exec isa privC s t s' ∧ abiPreserved s s' ∧ chkContract.post s s')
    (hspC : SpSafe privC) (hdC : privC.x86_64Depth ≤ Rsa.X86_64.stackBytes) {s : State}
    (h : (signK G).pre s) :
    WP isa (signC encN encC privN privC) s fun s' => (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧ (signK G).post s s' ∧
      s'.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10 := by
  have hp := SPre.of G h
  have hF := fb_toNat hp
  have hk1 := hp.k1; have hk2 := hp.k2
  refine wp_frame (by have := hp.sp1; unfold signStack Rsa.X86_64.stackBytes frameBytes at *; omega_arith) ?_
  rw [signCBody]
  simp only [seqs]
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono_mx (by decide) (signPro_ok hp) fun t1 ⟨k1, L1, R1, f1⟩ hx1 => ?_
  refine WP.mono_mx (by decide) (n0_ok hp L1 R1 (by simp [proW, upd]) k1.2.1 (frame_wrR f1))
    fun t2 ⟨k2, hm2, hax2, hz2⟩ hx2 => ?_
  have L2 : Lay t2 (fb s) (stackArg s 13) := L1.congr (k2.gpr (by decide)) k2.2.2 (by rw [hm2])
  have R2 : Rep t2.mem (fb s) (stackArg s 13) _ (proW s) := hm2 ▸ R1
  have hM2 : Frame (wrR s) s.mem t2.mem := hm2 ▸ frame_wrR f1
  have hw2 : t2.wr = frR s :: s.wr := k2.2.2.trans k1.2.2
  have hrd2 : t2.rd = s.rd := k2.2.1.trans k1.2.1
  have hcs2 : ∀ r ∈ [Reg.r13, .r14, .r15], t2.gpr r = s.gpr r := fun r hr => by
    have : r ∉ [Reg.rsi, .rax] := by simp at hr ⊢; rcases hr with rfl | rfl | rfl <;> simp
    rw [k2.gpr this, k1.gpr (by simp at hr ⊢; rcases hr with rfl | rfl | rfl <;> simp)]
    simp only [allocState_gpr']; rw [ifn (by simp at hr; rcases hr with rfl | rfl | rfl <;> simp)]
  refine WP.seq (WP.mono (Q := SDone G s) ?_ fun t3 D => restore_ok hp D)
  -- The modulus as `n₀ ‖ rest`.
  set n₀ := s.mem (s.gpr .rdx) with hn₀
  set rest := Spec.Rsa.bytesAt s.mem (s.gpr .rdx + 1) ((s.gpr .rcx).toNat - 1) with hrest
  have hnB : Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat = n₀ :: rest := bytesAt_cons _ _ (by omega_arith)
  have hrl : rest.length = (s.gpr .rcx).toNat - 1 := by simp [hrest, Spec.Rsa.bytesAt]
  refine WP.ite (M := isa) _ (show isa.eval .e t2 = _ from hz2) (fun hb => ?_) (fun hb => ?_)
  · -- `n₀ = 0`: refused.
    rw [decide_eq_true_eq] at hb
    have h0 : n₀ = 0 := BitVec.eq_of_toNat_eq hb
    refine fail_done hp L2 R2 hw2 hcs2 (by simp [proW, upd]) (by simp [proW, upd]) (by simp [proW, upd])
      (by simp [proW, upd]) (by simp [proW, upd]) ?_ (by rw [hx2, hx1]; rfl)
    rw [signOut, hnB, h0]; exact RsaPss.sign_zero ..
  rw [decide_eq_false_iff_not] at hb
  have h0 : n₀ ≠ 0 := fun h => hb (by rw [h]; rfl)
  have hl8 := RsaPss.log2_lt8 n₀
  set k := (s.gpr .rcx).toNat with hk
  set eb := ebV k n₀.toNat with heb_def
  set el := Spec.RsaPss.emLength eb with hel_def
  set lo := k - el with hlo_def
  have hlo : lo ≤ 1 := lo_le hl8 (by omega_arith)
  have heb : Spec.RsaPss.bitLength (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) k)) - 1 = eb := by
    rw [hnB, RsaPss.emBits_eq rest h0, hrl]; rfl
  have heb1 : 1 ≤ eb := by rw [heb_def]; unfold ebV; omega_arith
  have heb2 : eb ≤ Proof.RsaPss.maxEmBits := by
    rw [heb_def]; unfold ebV Proof.RsaPss.maxEmBits; omega_arith
  have hlok : lo + el = k := by
    rw [hlo_def, hel_def, heb_def]; unfold Spec.RsaPss.emLength ebV; omega_arith
  -- `emBits` and `encode`'s arguments.
  refine WP.seq (WP.mono_mx (by decide) (WP.keepIn (by decide) (by exact Nat.zero_le 8)
    (encPrep_ok L2 R2 (by simp [proW, upd]) (by simp [proW, upd]) (by simp [proW, upd])
      (by simp [proW, upd]) (by simp [proW, upd]) (by omega_arith) hk2 n₀.isLt hb hax2))
    fun t4 ⟨⟨L4, k4, R4, h4di, h4si, h4dx, h4cx, h48, h49⟩, f4⟩ hx4 => ?_)
  have hw4 : t4.wr = frR s :: s.wr := k4.2.2.trans hw2
  have hrd4 : t4.rd = s.rd := k4.2.1.trans hrd2
  have hM4 : Frame (wrR s) s.mem t4.mem := frame_keep hp hw2 L2.rsp hM2 f4
  -- `encode`.
  refine WP.seq (WP.mono (enc_call (G := G) hvE hspE hdE hp L4.rsp hrd4 hw4 hM4 R4 (lo := lo) (eb := eb) (el := el)
    ((R4.fr 0 (by decide)).trans (by simp [encW, upd])) ((R4.fr 1 (by decide)).trans (by simp [encW, upd]))
    h4di h4si h4dx h4cx h48 h49 hlo heb1 heb2 rfl) fun t5 ⟨rd5, wr5, cs5, mx5, hM5, R5, hE⟩ => ?_)
  set V5 := fun o => if inR [(oEm + lo, el), (oEnc, oRsa - oEnc)] o then t5.mem (off (stackArg s 13) o)
    else upd (fun o => s.mem (off (stackArg s 13) o)) oEm 0 o with hV5
  have L5 : Lay t5 (fb s) (stackArg s 13) := L4.of_rep' R4 R5 rfl (cs5 .rsp (by decide)) wr5
  -- Its result, tested.
  refine WP.seq (WP.mono_mx (by decide) (test32_ok t5) fun t6 ⟨k6, hm6, hz6⟩ hx6 => ?_)
  have L6 : Lay t6 (fb s) (stackArg s 13) := L5.congr (k6.gpr (by decide)) k6.2.2 (by rw [hm6])
  have R6 : Rep t6.mem (fb s) (stackArg s 13) V5 (encW (proW s) s eb) := by rw [hm6]; exact R5
  have hM6 : Frame (wrR s) s.mem t6.mem := by rw [hm6]; exact hM5
  have hw6 : t6.wr = frR s :: s.wr := k6.2.2.trans (wr5.trans hw4)
  have hrd6 : t6.rd = s.rd := k6.2.1.trans (rd5.trans hrd4)
  have hcs6 : ∀ r ∈ [Reg.r13, .r14, .r15], t6.gpr r = s.gpr r := fun r hr => by
    have h1 : r ∈ calleeSaved := by simp at hr; rcases hr with rfl | rfl | rfl <;> decide
    rw [k6.gpr (by simp at hr ⊢; rcases hr with rfl | rfl | rfl <;> simp), cs5 r h1,
      k4.gpr (by simp at hr ⊢; rcases hr with rfl | rfl | rfl <;> simp), hcs2 r hr]
  have hmx6 : t6.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10 := by rw [hx6, mx5, hx4, hx2, hx1]; rfl
  refine WP.ite (M := isa) _ (show isa.eval .e t6 = _ from hz6) (fun hb6 => ?_) (fun hb6 => ?_)
  · -- No encoding: refused.
    rw [decide_eq_true_eq] at hb6
    refine fail_done hp L6 R6 hw6 hcs6 (by simp [encW, proW, upd]) (by simp [encW, proW, upd])
      (by simp [encW, proW, upd]) (by simp [encW, proW, upd]) (by simp [encW, proW, upd]) ?_ hmx6
    rw [signOut, RsaPss.sign_encode G heb]
    cases he : Spec.RsaPss.encode G G (Spec.Rsa.bytesAt s.mem (stackArg s 10) G.len)
      (Spec.Rsa.bytesAt s.mem (stackArg s 11) (stackArg s 12).toNat) eb with
    | none => rfl
    | some e =>
      rw [he] at hE
      obtain ⟨h1, -⟩ := hE
      exact absurd (hb6.symm.trans h1) (by decide)
  rw [decide_eq_false_iff_not] at hb6
  obtain ⟨e, he, hbytes⟩ : ∃ e, Spec.RsaPss.encode G G (Spec.Rsa.bytesAt s.mem (stackArg s 10) G.len)
      (Spec.Rsa.bytesAt s.mem (stackArg s 11) (stackArg s 12).toNat) eb = some e ∧
      Spec.Rsa.bytesAt t5.mem (off (stackArg s 13) (oEm + lo)) el = e := by
    cases he : Spec.RsaPss.encode G G (Spec.Rsa.bytesAt s.mem (stackArg s 10) G.len)
      (Spec.Rsa.bytesAt s.mem (stackArg s 11) (stackArg s 12).toNat) eb with
    | none => rw [he] at hE; exact absurd hE hb6
    | some e => rw [he] at hE; exact ⟨e, rfl, hE.2⟩
  -- The private-key operation's arguments.
  refine WP.seq (WP.mono_mx (by decide) (WP.keepIn (by decide) (by exact Nat.zero_le 8)
    (privArgs_ok hp L6 hrd6 (argsKept_of hp hM6) R6 (by simp [encW, proW, upd]) (by simp [encW, proW, upd])
      (by simp [encW, proW, upd]) (by simp [encW, proW, upd]) (by simp [encW, proW, upd])
      (by simp [encW, proW, upd])))
    fun u2 ⟨⟨k7, L7, ⟨W2, R7, hW2a, hW2b⟩, h2di, h2si, h2dx, h2cx, h2r8, h2r9⟩, f7⟩ hx7 => ?_)
  have hw7 : u2.wr = frR s :: s.wr := k7.2.2.trans hw6
  have hM7 := frame_keep hp hw6 L6.rsp hM6 f7
  -- The call.
  refine WP.mono (priv_call hv hspC hdC hp L7.rsp (k7.2.1.trans hrd6) hw7 hM7
    (fun i hi => (R7.fr i (by unfold nW frameBytes; omega_arith)).trans (hW2a i hi)) h2di h2si h2dx h2cx h2r8 h2r9)
    fun u3 ⟨rd3, wr3, cs3, mx3, _, hk3, hout3⟩ => ?_
  have R3 : Rep u3.mem (fb s) (stackArg s 13) V5 W2 := R7.of_keep L7.geo fun x hx => hk3 x hx
  have L3 : Lay u3 (fb s) (stackArg s 13) := L7.of_rep' R7 R3 rfl (cs3 .rsp (by decide)) wr3
  have w : ∀ j, 40 < j → j < nW → W2 j = proW s j := fun j h hj => by
    rw [hW2b j hj (by omega_arith)]; simp only [encW, upd]
    rw [ifn (by omega_arith), ifn (by omega_arith), ifn (by omega_arith), ifn (by omega_arith), ifn (by omega_arith)]
  refine ⟨L3, wr3.trans hw7, fun r hr => ?_, ?_, ?_, ?_, ?_, by rw [mx3, hx7]; exact hmx6⟩
  · have hr3 : r = .r13 ∨ r = .r14 ∨ r = .r15 := by simpa using hr
    have h1 : r ∈ calleeSaved := by rcases hr3 with rfl | rfl | rfl <;> decide
    have h2 : r ∉ [Reg.rax, .rdi, .rsi, .rdx, .rcx, .r8, .r9] := by rcases hr3 with rfl | rfl | rfl <;> decide
    rw [cs3 r h1, k7.gpr h2, hcs6 r hr]
  · rw [R3.rd (d := sRbx) 41 rfl (by decide), w 41 (by decide) (by decide)]; simp [proW, upd]
  · rw [R3.rd (d := sRbp) 42 rfl (by decide), w 42 (by decide) (by decide)]; simp [proW, upd]
  · rw [R3.rd (d := sR12) 43 rfl (by decide), w 43 (by decide) (by decide)]; simp [proW, upd]
  · have hem : Spec.Rsa.bytesAt u2.mem (off (stackArg s 13) oEm) k = Spec.RsaPss.zeros lo ++ e := by
      rw [bytesAt_off, List.map_congr_left fun i hi => R7.scr _ (by have := List.mem_range.mp hi; unfold oEm oRsa; omega_arith)]
      exact em_input hlok hlo hbytes
    rw [hem] at hout3
    rw [signOut, RsaPss.sign_encode G heb, he, bytesAt_length]
    exact hout3

end VG.Proof.RsaPss.X86_64
