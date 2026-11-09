module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.RndCorrect
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.EncCorrect
import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.Bytes
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract

/-!
# RSAES-PKCS1-v1_5 encryption from a random tape on x86-64: the body and the contract

The first block leaves the state the scan starts from (`before_ok`); the
scan's two outcomes lead to the call (`accept_ok`) or to the request for
more entropy (`reject_ok`), and together they give `post` (`body_ok`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.X86_64.Rnd

open VG VG.X86_64 VG.Impl.RsaPkcs1Enc.X86_64.Random
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.RsaPkcs1Enc.X86_64 (encStack allocState_gpr allocState_mem word_ww byte freed wp_alloc)
open VG.Proof.Rsa.X86_64 (PublicImpl)

/-- The contract's postcondition, by name. -/
def post (s u : State) : Prop :=
  let res := Spec.RsaPkcs1Enc.padSearch (psLen s) (randB s)
  (∃ req, u.mem.readW (s.gpr .rdx) 64 = BitVec.ofNat 64 res.used ∧
    u.mem.readW (s.gpr .rdx + BitVec.ofNat 64 8) 64 = BitVec.ofNat 64 req ∧ res.Requests (cap s) req) ∧
  match res.outcome with
  | .accepted ps => Spec.Rsa.publicPrecompute (nB s) = some (preW s) →
      Spec.RsaPkcs1Enc.writtenRandom u.mem (s.gpr .rdi) (kOf s) ((u.gpr .rax).setWidth 32)
        (Spec.RsaPkcs1Enc.encrypt (nB s) (eB s) (msgB s) ps)
  | .entropy .. => (u.gpr .rax).setWidth 32 = 0 ∧
      Spec.Rsa.bytesAt u.mem (s.gpr .rdi) (kOf s) = List.replicate (kOf s) 0
  | .exhausted => (u.gpr .rax).setWidth 32 = 3 ∧
      Spec.Rsa.bytesAt u.mem (s.gpr .rdi) (kOf s) = List.replicate (kOf s) 0

/-! ## The first block -/

theorem setup_outside {s : State} (hp : RPre s) : Outside (fb s) 0 frameBytes s.mem (setupMem s) := by
  have hF := fb_toNat hp
  unfold setupMem
  refine Outside.ww (Outside.ww (Outside.ww (Outside.ww (Outside.ww (Outside.ww (Outside.refl _ _ _ _) _ ?_ ?_ ?_)
    _ ?_ ?_ ?_) _ ?_ ?_ ?_) _ ?_ ?_ ?_) _ ?_ ?_ ?_) _ ?_ ?_ ?_ <;>
    first | decide | (unfold frameBytes at *; omega)

theorem word_ww_ne (m : Mem) (base : Addr) {d d' : Nat} (v : BitVec 64)
    (h : decide ((d + 8 ≤ d' ∨ d' + 8 ≤ d) ∧ d + 8 ≤ 2 ^ 64 ∧ d' + 8 ≤ 2 ^ 64) = true) :
    word (m.writeW (off base d') v) base d = word m base d := by
  have h := of_decide_eq_true h
  exact word_ww m base v h.1 h.2.1 h.2.2

theorem setup_slots {s : State} : Slots s (setupMem s) := by
  unfold setupMem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp (disch := decide) only [word_writeW_self, word_ww_ne]

theorem before_ok {s : State} (hp : RPre s) : WP isa (.block setup) (allocState frameBytes s) fun t =>
    Before s t ∧ t.gpr .rcx = 0 ∧ t.gpr .rdx = 0 ∧ t.zf = some (stackArg s 4 == 0) ∧
    Keep [.rax, .rsi, .r11, .rdi, .rcx, .rdx] (allocState frameBytes s) t ∧ t.mxcsr = s.mxcsr := by
  refine WP.mono_mx (by decide) (setup_run hp) fun t ⟨hm, hsi, h11, hdi, hcx, hdx, hz, k⟩ hmx => ?_
  refine ⟨⟨⟨(k.gpr (by decide)).trans (by simp [allocState_gpr]), k.2.1, k.2.2, hm ▸ setup_outside hp,
    hm ▸ setup_slots⟩, hsi, h11, hdi⟩, hcx, hdx, hz, k, hmx⟩

/-- `PS` full after `i` octets: the state before the call's arguments. -/
theorem ready_of {s t₀ u : State} (hp : RPre s) (hb : Before s t₀) {i : Nat} (hI : At s t₀ i u)
    (hf : (kept s i).length = psLen s) : Ready s u i (kept s i) := by
  have hF := fb_toNat hp
  have hP := hp.ps
  refine ⟨⟨(hI.keep.gpr (by decide)).trans hb.rsp, hI.keep.2.1.trans hb.rd, hI.keep.2.2.trans hb.wr,
    hb.out.trans (hI.out.mono (by decide) (by unfold frameBytes oBuf; omega)), ?_⟩, hI.rcx,
    (hI.keep.gpr (by decide)).trans hb.rdi, hf, ?_, hI.hi⟩
  · have w : ∀ {d : Nat}, d + 8 ≤ oBuf → word u.mem (fb s) d = word t₀.mem (fb s) d := fun hd =>
      hI.out.word (.inl hd) (by unfold frameBytes oBuf at *; omega)
    exact ⟨(w (by decide)).trans hb.slots.sOut, (w (by decide)).trans hb.slots.sTape,
      (w (by decide)).trans hb.slots.sN, (w (by decide)).trans hb.slots.sK, (w (by decide)).trans hb.slots.sE,
      (w (by decide)).trans hb.slots.sPs⟩
  · rw [← hf]
    simp only [Spec.Rsa.bytesAt]
    apply List.ext_getElem (by simp)
    intro j h₁ _
    simp only [List.length_map, List.length_range] at h₁
    simp only [List.getElem_map, List.getElem_range]
    rw [show off (fb s) oBuf + BitVec.ofNat 64 j = off (fb s) (oBuf + j) from off_off _ _ _]
    have := hI.buf j h₁
    simp only [byte] at this
    rw [this]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h₁]

/-- Whether `PS` is full. -/
theorem full_ok {s t₀ u : State} (hp : RPre s) (hb : Before s t₀) {i : Nat} (hI : At s t₀ i u) :
    WP isa (.block [.alu .cmp .rdx (.mem (sp oPs))]) u fun v => v.mem = u.mem ∧ Keep [.rdx] u v ∧
      v.gpr .rdx = u.gpr .rdx ∧ v.zf = some (decide ((kept s i).length = psLen s)) := by
  have hF := fb_toNat hp
  have hP := hp.ps
  have hsp : u.gpr .rsp = fb s := (hI.keep.gpr (by decide)).trans hb.rsp
  have hs : Scr u (fb s) frameBytes := Scr.of_mem (by rw [hI.keep.2.2, hb.wr]; exact List.mem_cons_self ..)
    (by have := hF.1; omega)
  have hpsv : word u.mem (fb s) oPs = BitVec.ofNat 64 (psLen s) :=
    (hI.out.word (.inl (by decide)) (by unfold frameBytes oPs at *; omega)).trans hb.slots.sPs
  have hc := hI.hc
  refine WP.mono (WP.keep [.rdx] (Q := fun v => v.mem = u.mem ∧ v.gpr .rdx = u.gpr .rdx ∧
      v.zf = some (decide ((kept s i).length = psLen s))) (by
    xrun [ea_sp, hsp, fb_off, hs.ld (d := oPs) (by decide),
      show u.mem.readW (off (fb s) oPs) 64 = word u.mem (fb s) oPs from rfl, hpsv, hI.rdx,
      ofNat_beq (show (kept s i).length < 2 ^ 64 by omega) (show psLen s < 2 ^ 64 by omega)]) (by decide))
    fun v ⟨⟨hm, hd, hz⟩, k⟩ => ⟨hm, k, hd, hz⟩

/-- What every path leaves: the frame, and memory changed only where the
function may write. -/
structure Fin (s x : State) : Prop where
  rsp : x.gpr .rsp = fb s
  rd : x.rd = s.rd
  wr : x.wr = ⟨fb s, frameBytes⟩ :: s.wr
  fr : Frame [stkR s, tapeR s, outR s, scrR s] s.mem x.mem

theorem accept_ok (v : PublicImpl) {s t₀ u : State} (hp : RPre s) (hb : Before s t₀) {i : Nat}
    (hI : At s t₀ i u) (hf : (kept s i).length = psLen s)
    (hpre : Spec.RsaPkcs1Enc.nonzeroPrefix (psLen s) (randB s) = some (kept s i, i)) :
    WP isa (accept (encName v) (encCode v)) u fun x => Fin s x ∧ post s x ∧
      (∀ r ∈ calleeSaved, x.gpr r = u.gpr r) ∧ x.mxcsr.extractLsb' 6 10 = u.mxcsr.extractLsb' 6 10 := by
  have hr := ready_of hp hb hI hf
  refine WP.seq (WP.mono_mx (by decide) (prep_ok hp hr) fun w ⟨ha, k₁⟩ hmx₁ => ?_)
  refine WP.seq (WP.mono (call_ok v hp ha) fun u' ⟨hac, hcs, hmx₂⟩ => ?_)
  refine WP.mono_mx (by decide) (accTail_ok hp hac) fun x ⟨hsp, hrd, hwr, hfr, ht0, ht1, hres, k₃⟩ hmx₃ => ?_
  obtain ⟨ho, hu⟩ := VG.Proof.RsaPkcs1Enc.padSearch_accepted hpre
  refine ⟨⟨hsp, hrd, hwr, hfr⟩, ?_, fun r hr' => ?_, ?_⟩
  · show (∃ req, _ ∧ _ ∧ _) ∧ _
    rw [ho, hu]
    refine ⟨⟨0, ht0, ht1, ?_⟩, hres⟩
    unfold Spec.Entropy.Result.Requests
    rw [ho]
  · have hn : r ∉ [Reg.rax, .rcx, .rdi, .r10, .r11] := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have hn' : r ∉ [Reg.rax, .r10, .rdi, .rsi, .rdx, .rcx, .r8, .r9] := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [k₃.gpr hn, hcs r hr', k₁.gpr hn']
  · rw [hmx₃, hmx₂, hmx₁]

theorem kept_all (s : State) : kept s (stackArg s 4).toNat = VG.Proof.RsaPkcs1Enc.nz (randB s) := by
  simp only [kept]; rw [← randB_length, List.take_length]

theorem bytes_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨p, n⟩ : Region).Disjoint r) (hn : n ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt m' p n = Spec.Rsa.bytesAt m p n := by
  simp only [Spec.Rsa.bytesAt]
  exact List.map_congr_left fun j hj => hf.bytes (R := ⟨p, n⟩) hd hn (List.mem_range.mp hj)

theorem reject_ok {s t₀ u : State} (hp : RPre s) (hb : Before s t₀) (hI : At s t₀ (stackArg s 4).toNat u)
    (hc : (kept s (stackArg s 4).toNat).length < psLen s) :
    WP isa reject u fun x => Fin s x ∧ post s x ∧
      (∀ r ∈ calleeSaved, x.gpr r = u.gpr r) ∧ x.mxcsr.extractLsb' 6 10 = u.mxcsr.extractLsb' 6 10 := by
  have hF := fb_toNat hp
  have hP := hp.ps
  have hk2 := hp.k2
  have hrl := hp.randLen
  have hsp : u.gpr .rsp = fb s := (hI.keep.gpr (by decide)).trans hb.rsp
  have hwr : u.wr = ⟨fb s, frameBytes⟩ :: s.wr := hI.keep.2.2.trans hb.wr
  have hout : Outside (fb s) 0 frameBytes s.mem u.mem :=
    hb.out.trans (hI.out.mono (by decide) (by unfold frameBytes oBuf; omega))
  have hsl : Slots s u.mem := by
    have w : ∀ {d : Nat}, d + 8 ≤ oBuf → word u.mem (fb s) d = word t₀.mem (fb s) d := fun hd =>
      hI.out.word (.inl hd) (by unfold frameBytes oBuf at *; omega)
    exact ⟨(w (by decide)).trans hb.slots.sOut, (w (by decide)).trans hb.slots.sTape,
      (w (by decide)).trans hb.slots.sN, (w (by decide)).trans hb.slots.sK, (w (by decide)).trans hb.slots.sE,
      (w (by decide)).trans hb.slots.sPs⟩
  refine WP.mono_mx (Q := fun x => Fin s x ∧ post s x ∧ (∀ r ∈ calleeSaved, x.gpr r = u.gpr r)) (by decide) ?_
    fun x h hmx => ⟨h.1, h.2.1, h.2.2, by rw [hmx]⟩
  refine WP.seq (WP.mono (zeroOut_ok hp hsp hwr hsl) fun u₁ ⟨f₁, z₁, k₁⟩ => ?_)
  have slotOut : ∀ {d : Nat}, d + 8 ≤ frameBytes → (⟨off (fb s) d, 8⟩ : Region).Disjoint (outR s) :=
    fun hd => hp.dKo.sub_left (frame_sub s hd)
  have sl₁ : Slots s u₁.mem := by
    have w : ∀ {d : Nat}, d + 8 ≤ frameBytes → word u₁.mem (fb s) d = word u.mem (fb s) d := fun hd =>
      f₁.readW (Region.contains_self _ _) (fun r hr => by rw [List.mem_singleton.mp hr]; exact slotOut hd)
        (by decide)
    exact ⟨(w (by decide)).trans hsl.sOut, (w (by decide)).trans hsl.sTape, (w (by decide)).trans hsl.sN,
      (w (by decide)).trans hsl.sK, (w (by decide)).trans hsl.sE, (w (by decide)).trans hsl.sPs⟩
  have hdx₁ : u₁.gpr .rdx = BitVec.ofNat 64 (kept s (stackArg s 4).toNat).length := (k₁.gpr (by decide)).trans hI.rdx
  refine WP.seq (WP.mono (wipeDrawn_ok hp ((k₁.gpr (by decide)).trans hsp) (k₁.2.2.trans hwr) hc hdx₁)
    fun u₂ ⟨f₂, k₂, hdx₂⟩ => ?_)
  have bufD : ∀ {d : Nat}, d + 8 ≤ oBuf → (⟨off (fb s) d, 8⟩ : Region).Disjoint ⟨off (fb s) oBuf, (kept s (stackArg s 4).toNat).length⟩ :=
    fun hd => Offset.disjoint (fb s) (.inl hd) (by unfold frameBytes oBuf at *; omega)
      (by unfold frameBytes oBuf at *; omega)
  have sl₂ : Slots s u₂.mem := by
    have w : ∀ {d : Nat}, d + 8 ≤ oBuf → word u₂.mem (fb s) d = word u₁.mem (fb s) d := fun hd =>
      f₂.readW (Region.contains_self _ _) (fun r hr => by rw [List.mem_singleton.mp hr]; exact bufD hd)
        (by decide)
    exact ⟨(w (by decide)).trans sl₁.sOut, (w (by decide)).trans sl₁.sTape, (w (by decide)).trans sl₁.sN,
      (w (by decide)).trans sl₁.sK, (w (by decide)).trans sl₁.sE, (w (by decide)).trans sl₁.sPs⟩
  have k₁₂ := k₁.trans k₂
  have h11 : u₂.gpr .r11 = stackArg s 4 :=
    (k₁₂.gpr (by decide)).trans ((hI.keep.gpr (by decide)).trans hb.r11)
  refine WP.mono (budget_ok hp ((k₁₂.gpr (by decide)).trans hsp) (k₁₂.2.2.trans hwr) sl₂ hc
    (hdx₂.trans hdx₁) h11) fun x ⟨f₃, k₃, hex, hen⟩ => ?_
  have k := k₁₂.trans k₃
  -- memory
  have bufS : Region.Sub ⟨off (fb s) oBuf, (kept s (stackArg s 4).toNat).length⟩ (stkR s) := frame_sub s (by unfold frameBytes oBuf; omega)
  have hfr : Frame [stkR s, tapeR s, outR s, scrR s] s.mem x.mem :=
    ((((frame_of_outside hout).mono (by simp)).trans (f₁.mono (by simp))).trans
      (f₂.sub fun r hr => by rw [List.mem_singleton.mp hr]; exact ⟨stkR s, by simp, bufS⟩)).trans
      (f₃.mono (by simp))
  have outZ : Spec.Rsa.bytesAt x.mem (s.gpr .rdi) (kOf s) = List.replicate (kOf s) 0 := by
    have e : (⟨s.gpr .rdi, kOf s⟩ : Region) = outR s := by rw [outR, hp.hsi]; rfl
    rw [bytes_frame f₃ (fun r hr => by rw [List.mem_singleton.mp hr, e]; exact hp.dOt) (by unfold kOf; omega),
      bytes_frame f₂ (fun r hr => by
        rw [List.mem_singleton.mp hr, e]; exact fun y h₁ h₂ => hp.dKo y (bufS y h₂) h₁) (by unfold kOf; omega), z₁]
  refine ⟨⟨(k.gpr (by decide)).trans hsp, k.2.1.trans (hI.keep.2.1.trans hb.rd), k.2.2.trans hwr, hfr⟩, ?_,
    fun r hr' => ?_⟩
  · have hnz : (VG.Proof.RsaPkcs1Enc.nz (randB s)).length < psLen s := by rw [← kept_all]; exact hc
    show (∃ req, _ ∧ _ ∧ _) ∧ _
    unfold Spec.Entropy.Result.Requests
    have hcap : cap s = Spec.RsaPkcs1Enc.padEntropy (psLen s) := rfl
    by_cases hge : cap s ≤ (stackArg s 4).toNat
    · obtain ⟨ho, hu⟩ := VG.Proof.RsaPkcs1Enc.padSearch_exhausted hnz (by rw [randB_length]; exact hge)
      obtain ⟨h0, h1, hr⟩ := hex hge
      rw [ho, hu, randB_length]
      exact ⟨⟨0, by rw [h0]; simp, h1, rfl⟩, hr, outZ⟩
    · obtain ⟨ho, hu⟩ := VG.Proof.RsaPkcs1Enc.padSearch_entropy hnz (by rw [randB_length]; omega)
      obtain ⟨h0, h1, hr⟩ := hen (by omega)
      rw [ho, hu]
      refine ⟨⟨_, h0, h1, ?_⟩, hr, outZ⟩
      rw [randB_length]
      constructor
      · simp only [Nat.lt_min]; constructor <;> unfold cap Spec.RsaPkcs1Enc.padEntropy at * <;> omega
      · exact Nat.min_le_left _ _
  · have hn : r ∉ [Reg.rdi, .r10, .rax] ++ [Reg.rdi, .r10, .rcx, .rdx] ++ [Reg.rax, .r8, .r9, .r10, .r11] := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact k.gpr hn

/-! ## The whole function -/

theorem ret_apart {s : State} (hp : RPre s) {m : Mem} (h : Frame [stkR s, tapeR s, outR s, scrR s] s.mem m) :
    m.readW (s.gpr .rsp) 64 = s.mem.readW (s.gpr .rsp) 64 := by
  have hK := kb_toNat hp
  refine h.readW (r := retR s) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [stkR_eq, retR, show s.gpr .rsp = off (kb s) rndStack by
      simp only [off, kb]; exact (BitVec.sub_add_cancel _ _).symm]
    exact (Offset.base_disjoint (kb s) (e := rndStack) (n := 8) (k := rndStack) (Nat.le_refl _)
      (by omega)).symm
  · exact hp.dXt
  · exact hp.dXo
  · exact hp.dXs

theorem body_ok (v : PublicImpl) {s : State} (hp : RPre s) :
    WP isa (body (encName v) (encCode v)) (allocState frameBytes s) fun x => Fin s x ∧ post s x ∧
      (∀ r ∈ calleeSaved, r ≠ .rsp → x.gpr r = s.gpr r) ∧
      x.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10 := by
  refine WP.seq (WP.mono (before_ok hp) fun t₁ ⟨hb, hcx, hdx, hz, k₁, hmx₁⟩ => ?_)
  refine WP.seq (WP.mono_mx (by decide) (scan_ok hp hb hcx hdx hz) fun u ⟨i, hI, hres⟩ hmx₂ => ?_)
  refine WP.seq (WP.mono_mx (by decide) (full_ok hp hb hI) fun w ⟨hm, kw, hd, hzw⟩ hmx₃ => ?_)
  have hI' : At s t₁ i w := ⟨(hI.keep.trans kw).mono (by decide), hm ▸ hI.out, hm ▸ hI.buf,
    (kw.gpr (by decide)).trans hI.rcx, hd.trans hI.rdx, hI.hi, hI.hc⟩
  have cs : ∀ r ∈ calleeSaved, r ≠ .rsp → w.gpr r = s.gpr r := fun r hr hr' => by
    have hn : r ∉ [Reg.rax, .rsi, .r11, .rdi, .rcx, .rdx] ++ ([Reg.rax, .rcx, .rdx] ++ [Reg.rdx]) := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | decide | exact absurd rfl hr'
    rw [(k₁.trans (hI.keep.trans kw)).gpr hn]
    simp [allocState_gpr, hr']
  rcases hres with ⟨hf, hpre⟩ | ⟨hi, hc⟩
  · refine WP.ite true (by rw [eval_e hzw, decide_eq_true hf]) (fun _ => ?_) (fun h => absurd h (by decide))
    refine WP.mono (accept_ok v hp hb hI' hf hpre) fun x ⟨hfin, hpost, hcs, hmx⟩ =>
      ⟨hfin, hpost, fun r hr hr' => (hcs r hr).trans (cs r hr hr'), ?_⟩
    rw [hmx, hmx₃, hmx₂, hmx₁]
  · subst hi
    refine WP.ite false (by rw [eval_e hzw, decide_eq_false (by omega)]) (fun h => absurd h (by decide))
      fun _ => ?_
    refine WP.mono (reject_ok hp hb hI' hc) fun x ⟨hfin, hpost, hcs, hmx⟩ =>
      ⟨hfin, hpost, fun r hr hr' => (hcs r hr).trans (cs r hr hr'), ?_⟩
    rw [hmx, hmx₃, hmx₂, hmx₁]

theorem code_correct (v : PublicImpl) (s : State)
    (h : (Spec.RsaPkcs1Enc.encryptRandomContract abi rndStack).pre s) :
    ∃ t s', Exec isa (code (encName v) (encCode v)) s t s' ∧ abiPreserved s s' ∧ post s s' := by
  have hp := pre_of h
  suffices hw : WP isa (code (encName v) (encCode v)) s fun s' => abiPreserved s s' ∧ post s s' by
    obtain ⟨t, s', he, hq⟩ := hw
    exact ⟨t, s', he, hq⟩
  refine wp_alloc (by decide) (by decide) (by decide) (by have := hp.sp1; unfold rndStack at this; omega) ?_
  refine WP.mono (body_ok v hp) fun x ⟨hfin, hpost, hcs, hmx⟩ => ⟨hfin.rsp, by rw [hfin.wr]; rfl, ?_, hpost⟩
  refine ⟨fun r hr => ?_, ret_apart hp hfin.fr, hmx⟩
  by_cases hr' : r = .rsp
  · subst hr'
    show x.gpr .rsp + BitVec.ofNat 64 frameBytes = s.gpr .rsp
    rw [hfin.rsp, BitVec.sub_add_cancel]
  · show (if r = .rsp then _ else x.gpr r) = s.gpr r
    simp only [hr', ↓reduceIte]
    exact hcs r hr hr'

end VG.Proof.RsaPkcs1Enc.X86_64.Rnd

/-!
## The contract

`contract` is the shared contract's precondition, `post`, and its public data
by name (`pub`); it implies the shared contract (`implies`).
-/

namespace VG.Proof.RsaPkcs1Enc.X86_64.Rnd

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

/-- The trace of drawing `PS`. -/
abbrev trace (s : State) : List Nat := (Spec.RsaPkcs1Enc.padSearch (psLen s) (randB s)).trace

/-- The public data, by name. -/
def pub (a s : State) : Prop :=
  a.gpr .rsp = s.gpr .rsp ∧ (∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9], a.gpr r = s.gpr r) ∧
    (∀ j < 9, stackArg a j = stackArg s j) ∧ nB a = nB s ∧ eB a = eB s ∧ preW a = preW s ∧ trace a = trace s

def contract : Contract isa where
  pre := (Spec.RsaPkcs1Enc.encryptRandomContract abi rndStack).pre
  post := post
  pub := pub

theorem wordsAt_two (m : Mem) (p : Addr) :
    Spec.Rsa.wordsAt m p 2 = [m.readW p 64, m.readW (p + BitVec.ofNat 64 8) 64] := by
  simp [Spec.Rsa.wordsAt, List.range_succ]

/-- A state meeting the precondition: a 512-bit key, an empty message and tape. -/
def satState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 64 | .rdx => 0x2000 | .rcx => 0x3000 | .r8 => 64 | .r9 => 0x4000
    | .rsp => 0x10000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x10008 then 1 else if a = 0x10011 then 0x50 else if a = 0x10021 then 0x60
    else if a = 0x10032 then 0x02 else if a = 0x10038 then 0x70 else if a = 0x10041 then 0x70
    else if a = 0x10048 then 0x10 else 0
  rd := [⟨0x3000, 64⟩, ⟨0x4000, 1⟩, ⟨0x5000, 0⟩, ⟨0x6000, 0⟩, ⟨0x7000, 128⟩, ⟨0x10008, 72⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x2000, 16⟩, ⟨0x20000, 896⟩]

theorem implies : contract.Implies (Spec.RsaPkcs1Enc.encryptRandomContract abi rndStack) where
  pre := fun _ h => h
  post := by
    intro s u _ h
    sig_post [Spec.RsaPkcs1Enc.encryptRandomContract, Spec.RsaPkcs1Enc.encryptRandomSig,
      abi, argRegs, stackArgs_nine, List.append_eq, List.range, List.range.loop]
    obtain ⟨⟨req, h0, h1, hr⟩, hm⟩ := h
    exact ⟨⟨req, by rw [wordsAt_two, h0, h1]; rfl, hr⟩, hm⟩
  pub := by
    rintro s₁ s₂ - - h
    sig_pub [Spec.RsaPkcs1Enc.encryptRandomContract, Spec.RsaPkcs1Enc.encryptRandomSig,
      abi, argRegs, stackArgs_nine, List.append_eq, List.range, List.range.loop] at h
    obtain ⟨hsp, hl, hdi, hsi, hdx, hcx, h8, h9, a0, a1, a2, a3, a4, a5, a6, a7, a8⟩ := h
    have hl' : (List.map BitVec.toNat (nB s₁ ++ eB s₁) ++ List.map BitVec.toNat (preW s₁)) ++ trace s₁ =
        (List.map BitVec.toNat (nB s₂ ++ eB s₂) ++ List.map BitVec.toNat (preW s₂)) ++ trace s₂ := hl
    have hl1 : (List.map BitVec.toNat (nB s₁ ++ eB s₁)).length =
        (List.map BitVec.toNat (nB s₂ ++ eB s₂)).length := by
      simp [nB, eB, kOf, Spec.Rsa.bytesAt, h8, a0]
    have hl2 : (List.map BitVec.toNat (preW s₁)).length = (List.map BitVec.toNat (preW s₂)).length := by
      simp [preW, Spec.Rsa.wordsAt, a8]
    obtain ⟨h12, h3⟩ := List.append_inj hl' (by simp only [List.length_append, hl1, hl2])
    obtain ⟨h1, h2⟩ := List.append_inj h12 hl1
    have inj : ∀ {w : Nat} {l₁ l₂ : List (BitVec w)}, l₁.map BitVec.toNat = l₂.map BitVec.toNat → l₁ = l₂ :=
      fun h => (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 h
    have hne := inj h1
    obtain ⟨hn, he⟩ := List.append_inj hne (by simp [nB, kOf, Spec.Rsa.bytesAt, h8])
    refine ⟨hsp, ?_, fun j hj => ?_, hn, he, inj h2, h3⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl | rfl | rfl | rfl | rfl) <;> with_reducible assumption
    · match j, hj with
      | 0, _ => exact a0 | 1, _ => exact a1 | 2, _ => exact a2 | 3, _ => exact a3 | 4, _ => exact a4
      | 5, _ => exact a5 | 6, _ => exact a6 | 7, _ => exact a7 | 8, _ => exact a8
  sat := by
    implies_sat [Spec.RsaPkcs1Enc.encryptRandomContract, Spec.RsaPkcs1Enc.encryptRandomSig, abi, argRegs,
      stackArgs_nine, List.append_eq, rndStack, frameBytes, VG.Proof.RsaPkcs1Enc.X86_64.encStack,
      Impl.RsaPkcs1Enc.X86_64.Encrypt.frameBytes]
      [satState, stackArg, stackArgAddr, Mem.readW, Mem.read] using satState

end VG.Proof.RsaPkcs1Enc.X86_64.Rnd
