module

-- separate module: its proofs build in parallel with `RndHeads`
public import VerifiedGarbage.Proof.RsaPkcs1Enc.RandomCT
public import VerifiedGarbage.Proof.Bignum.X86_64.Mont
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.RandomCT
meta import VerifiedGarbage.Proof.Bignum.X86_64.Mont
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.RndCorrect
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.EncCorrect
import VerifiedGarbage.Proof.Rsa.BytesFrame
import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.EncFrame
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.RndCorrect
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.EncCorrect
meta import VerifiedGarbage.Proof.Rsa.BytesFrame
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.EncFrame
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Contract

/-! ### `RsaPkcs1Enc.X86_64.RndContract`, which only this module used -/

section

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
  obtain h := of_decide_eq_true h
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
  obtain hF := fb_toNat hp
  have hP := hp.ps
  refine ⟨⟨(hI.keep.gpr (by decide)).trans hb.rsp, hI.keep.2.1.trans hb.rd, hI.keep.2.2.trans hb.wr,
    hb.out.trans (hI.out.mono (by decide) (by unfold frameBytes oBuf; omega_using [hf, hP])), ?_⟩, hI.rcx,
    (hI.keep.gpr (by decide)).trans hb.rdi, hf, ?_, hI.hi⟩
  · have w : ∀ {d : Nat}, d + 8 ≤ oBuf → word u.mem (fb s) d = word t₀.mem (fb s) d := fun hd =>
      hI.out.word (.inl hd) (by unfold frameBytes oBuf at *; omega_using [hd])
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
  obtain hF := fb_toNat hp
  have hP := hp.ps
  obtain hsp : u.gpr .rsp = fb s := (hI.keep.gpr (by decide)).trans hb.rsp
  obtain hs : Scr u (fb s) frameBytes := Scr.of_mem (by rw [hI.keep.2.2, hb.wr]; exact List.mem_cons_self ..)
    (by have := hF.1; omega_using [hF])
  obtain hpsv : word u.mem (fb s) oPs = BitVec.ofNat 64 (psLen s) :=
    (hI.out.word (.inl (by decide)) (by unfold frameBytes oPs at *; omega_using [])).trans hb.slots.sPs
  have hc := hI.hc
  refine WP.mono (WP.keep [.rdx] (Q := fun v => v.mem = u.mem ∧ v.gpr .rdx = u.gpr .rdx ∧
      v.zf = some (decide ((kept s i).length = psLen s))) (by
    xrun [ea_sp, hsp, fb_off, hs.ld (d := oPs) (by decide),
      show u.mem.readW (off (fb s) oPs) 64 = word u.mem (fb s) oPs from rfl, hpsv, hI.rdx,
      ofNat_beq (show (kept s i).length < 2 ^ 64 by omega_using [hP, hc]) (show psLen s < 2 ^ 64 by omega_using [hP])]) (by decide))
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
  obtain hr := ready_of hp hb hI hf
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
    obtain hn' : r ∉ [Reg.rax, .r10, .rdi, .rsi, .rdx, .rcx, .r8, .r9] := by
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
  obtain hF := fb_toNat hp
  have hP := hp.ps
  have hk2 := hp.k2
  have hrl := hp.randLen
  obtain hsp : u.gpr .rsp = fb s := (hI.keep.gpr (by decide)).trans hb.rsp
  obtain hwr : u.wr = ⟨fb s, frameBytes⟩ :: s.wr := hI.keep.2.2.trans hb.wr
  obtain hout : Outside (fb s) 0 frameBytes s.mem u.mem :=
    hb.out.trans (hI.out.mono (by decide) (by unfold frameBytes oBuf; omega_using [hc, hP]))
  obtain hsl : Slots s u.mem := by
    obtain w : ∀ {d : Nat}, d + 8 ≤ oBuf → word u.mem (fb s) d = word t₀.mem (fb s) d := fun hd =>
      hI.out.word (.inl hd) (by unfold frameBytes oBuf at *; omega_using [hd])
    exact ⟨(w (by decide)).trans hb.slots.sOut, (w (by decide)).trans hb.slots.sTape,
      (w (by decide)).trans hb.slots.sN, (w (by decide)).trans hb.slots.sK, (w (by decide)).trans hb.slots.sE,
      (w (by decide)).trans hb.slots.sPs⟩
  refine WP.mono_mx (Q := fun x => Fin s x ∧ post s x ∧ (∀ r ∈ calleeSaved, x.gpr r = u.gpr r)) (by decide) ?_
    fun x h hmx => ⟨h.1, h.2.1, h.2.2, by rw [hmx]⟩
  refine WP.seq (WP.mono (zeroOut_ok hp hsp hwr hsl) fun u₁ ⟨f₁, z₁, k₁⟩ => ?_)
  obtain slotOut : ∀ {d : Nat}, d + 8 ≤ frameBytes → (⟨off (fb s) d, 8⟩ : Region).Disjoint (outR s) :=
    fun hd => hp.dKo.sub_left (frame_sub s hd)
  obtain sl₁ : Slots s u₁.mem := by
    obtain w : ∀ {d : Nat}, d + 8 ≤ frameBytes → word u₁.mem (fb s) d = word u.mem (fb s) d := fun hd =>
      f₁.readW (Region.contains_self _ _) (fun r hr => by rw [List.mem_singleton.mp hr]; exact slotOut hd)
        (by decide)
    exact ⟨(w (by decide)).trans hsl.sOut, (w (by decide)).trans hsl.sTape, (w (by decide)).trans hsl.sN,
      (w (by decide)).trans hsl.sK, (w (by decide)).trans hsl.sE, (w (by decide)).trans hsl.sPs⟩
  obtain hdx₁ : u₁.gpr .rdx = BitVec.ofNat 64 (kept s (stackArg s 4).toNat).length := (k₁.gpr (by decide)).trans hI.rdx
  refine WP.seq (WP.mono (wipeDrawn_ok hp ((k₁.gpr (by decide)).trans hsp) (k₁.2.2.trans hwr) hc hdx₁)
    fun u₂ ⟨f₂, k₂, hdx₂⟩ => ?_)
  obtain bufD : ∀ {d : Nat}, d + 8 ≤ oBuf → (⟨off (fb s) d, 8⟩ : Region).Disjoint ⟨off (fb s) oBuf, (kept s (stackArg s 4).toNat).length⟩ :=
    fun hd => Offset.disjoint (fb s) (.inl hd) (by unfold frameBytes oBuf at *; omega_using [hd])
      (by unfold frameBytes oBuf at *; omega_using [hc, hP])
  obtain sl₂ : Slots s u₂.mem := by
    obtain w : ∀ {d : Nat}, d + 8 ≤ oBuf → word u₂.mem (fb s) d = word u₁.mem (fb s) d := fun hd =>
      f₂.readW (Region.contains_self _ _) (fun r hr => by rw [List.mem_singleton.mp hr]; exact bufD hd)
        (by decide)
    exact ⟨(w (by decide)).trans sl₁.sOut, (w (by decide)).trans sl₁.sTape, (w (by decide)).trans sl₁.sN,
      (w (by decide)).trans sl₁.sK, (w (by decide)).trans sl₁.sE, (w (by decide)).trans sl₁.sPs⟩
  obtain k₁₂ := k₁.trans k₂
  obtain h11 : u₂.gpr .r11 = stackArg s 4 :=
    (k₁₂.gpr (by decide)).trans ((hI.keep.gpr (by decide)).trans hb.r11)
  refine WP.mono (budget_ok hp ((k₁₂.gpr (by decide)).trans hsp) (k₁₂.2.2.trans hwr) sl₂ hc
    (hdx₂.trans hdx₁) h11) fun x ⟨f₃, k₃, hex, hen⟩ => ?_
  obtain k := k₁₂.trans k₃
  -- memory
  obtain bufS : Region.Sub ⟨off (fb s) oBuf, (kept s (stackArg s 4).toNat).length⟩ (stkR s) := frame_sub s (by unfold frameBytes oBuf; omega_using [hc, hP])
  obtain hfr : Frame [stkR s, tapeR s, outR s, scrR s] s.mem x.mem :=
    ((((frame_of_outside hout).mono (by simp)).trans (f₁.mono (by simp))).trans
      (f₂.sub fun r hr => by rw [List.mem_singleton.mp hr]; exact ⟨stkR s, by simp, bufS⟩)).trans
      (f₃.mono (by simp))
  obtain outZ : Spec.Rsa.bytesAt x.mem (s.gpr .rdi) (kOf s) = List.replicate (kOf s) 0 := by
    obtain e : (⟨s.gpr .rdi, kOf s⟩ : Region) = outR s := by rw [outR, hp.hsi]; rfl
    rw [bytes_frame f₃ (fun r hr => by rw [List.mem_singleton.mp hr, e]; exact hp.dOt) (by unfold kOf; omega_using []),
      bytes_frame f₂ (fun r hr => by
        rw [List.mem_singleton.mp hr, e]; exact fun y h₁ h₂ => hp.dKo y (bufS y h₂) h₁) (by unfold kOf; omega_using []), z₁]
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
    · obtain ⟨ho, hu⟩ := VG.Proof.RsaPkcs1Enc.padSearch_entropy hnz (by rw [randB_length]; omega_using [hcap, hge])
      obtain ⟨h0, h1, hr⟩ := hen (by omega_using [hge])
      rw [ho, hu]
      refine ⟨⟨_, h0, h1, ?_⟩, hr, outZ⟩
      rw [randB_length]
      constructor
      · simp only [Nat.lt_min]; constructor <;> unfold cap Spec.RsaPkcs1Enc.padEntropy at * <;> omega_arith
      · exact Nat.min_le_left _ _
  · have hn : r ∉ [Reg.rdi, .r10, .rax] ++ [Reg.rdi, .r10, .rcx, .rdx] ++ [Reg.rax, .r8, .r9, .r10, .r11] := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact k.gpr hn

/-! ## The whole function -/

theorem ret_apart {s : State} (hp : RPre s) {m : Mem} (h : Frame [stkR s, tapeR s, outR s, scrR s] s.mem m) :
    m.readW (s.gpr .rsp) 64 = s.mem.readW (s.gpr .rsp) 64 := by
  obtain hK := kb_toNat hp
  refine h.readW (r := retR s) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [stkR_eq, retR, show s.gpr .rsp = off (kb s) rndStack by
      simp only [off, kb]; exact (BitVec.sub_add_cancel _ _).symm]
    exact (Offset.base_disjoint (kb s) (e := rndStack) (n := 8) (k := rndStack) (Nat.le_refl _)
      (by omega_using [hK])).symm
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
  obtain hI' : At s t₁ i w := ⟨(hI.keep.trans kw).mono (by decide), hm ▸ hI.out, hm ▸ hI.buf,
    (kw.gpr (by decide)).trans hI.rcx, hd.trans hI.rdx, hI.hi, hI.hc⟩
  obtain cs : ∀ r ∈ calleeSaved, r ≠ .rsp → w.gpr r = s.gpr r := fun r hr hr' => by
    obtain hn : r ∉ [Reg.rax, .rsi, .r11, .rdi, .rcx, .rdx] ++ ([Reg.rax, .rcx, .rdx] ++ [Reg.rdx]) := by
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
    refine WP.ite false (by rw [eval_e hzw, decide_eq_false (by omega_using [hc])]) (fun h => absurd h (by decide))
      fun _ => ?_
    refine WP.mono (reject_ok hp hb hI' hc) fun x ⟨hfin, hpost, hcs, hmx⟩ =>
      ⟨hfin, hpost, fun r hr hr' => (hcs r hr).trans (cs r hr hr'), ?_⟩
    rw [hmx, hmx₃, hmx₂, hmx₁]

/-- `post`, whatever the bytes of a region of the stack hold. -/
theorem post_lost {s : State} (hp : RPre s) {u u' : State} (hg : u'.gpr = u.gpr) {R : Region}
    (f : Frame [R] u.mem u'.mem) (hR : R.Sub (stkR s)) (h : post s u) : post s u' := by
  have sep : ∀ {B : Region}, (stkR s).Disjoint B → ∀ q ∈ [R], B.Disjoint q := fun hd q hq => by
    simp only [List.mem_singleton] at hq; subst hq
    exact (hd.sub_left hR).symm
  have hsi := hp.hsi
  have hb : Spec.Rsa.bytesAt u'.mem (s.gpr .rdi) (kOf s) = Spec.Rsa.bytesAt u.mem (s.gpr .rdi) (kOf s) :=
    Proof.Rsa.rsa_bytes_frame f (s.gpr .r8).isLt (sep (by
      have := hp.dKo; simp only [outR, hsi] at this; exact this))
  have ht : ∀ d, d + 8 ≤ 16 → u'.mem.readW (s.gpr .rdx + BitVec.ofNat 64 d) 64 =
      u.mem.readW (s.gpr .rdx + BitVec.ofNat 64 d) 64 := fun d hd =>
    f.readW (r := tapeR s) (Offset.contains_base _ (by omega_using [hd]) (by omega_using [hd]))
      (sep hp.dKt) (by decide)
  have h0 := ht 0 (by decide)
  rw [BitVec.add_zero] at h0
  have hax : u'.gpr .rax = u.gpr .rax := by rw [hg]
  obtain ⟨⟨req, h1, h2, h3⟩, h4⟩ := h
  refine ⟨⟨req, by rw [h0]; exact h1, by rw [ht 8 (by decide)]; exact h2, h3⟩, ?_⟩
  revert h4
  cases (Spec.RsaPkcs1Enc.padSearch (psLen s) (randB s)).outcome
  case accepted ps =>
    intro h4 hpc
    have h5 := h4 hpc
    revert h5
    cases Spec.RsaPkcs1Enc.encrypt (nB s) (eB s) (msgB s) ps <;>
      simp only [Spec.RsaPkcs1Enc.writtenRandom] <;> rw [hb, hax] <;> exact id
  all_goals intro h4; rw [hb, hax]; exact h4

theorem code_correct (v : PublicImpl) (s : State)
    (h : (Spec.RsaPkcs1Enc.encryptRandomContract abi rndStack).pre s) :
    ∃ t s', Exec isa (code (encName v) (encCode v)) s t s' ∧ abiPreserved s s' ∧ post s s' := by
  obtain hp := pre_of h
  suffices hw : WP isa (code (encName v) (encCode v)) s fun s' => abiPreserved s s' ∧ post s s' by
    obtain ⟨t, s', he, hq⟩ := hw
    exact ⟨t, s', he, hq⟩
  refine wp_alloc (by decide) (by decide) (by decide) (by have := hp.sp1; unfold rndStack at this; omega_using [this]) ?_
  have hs := VG.Proof.RsaPkcs1Enc.X86_64.Rnd.frame_sub s (d := 0) (n := frameBytes) (by omega_using [])
  simp only [off, BitVec.add_zero] at hs
  refine WP.mono (body_ok v hp) fun x ⟨hfin, hpost, hcs, hmx⟩ => ⟨hfin.rsp, by rw [hfin.wr]; rfl,
    fun m u fm => ⟨?_, post_lost hp (u := freed frameBytes x) rfl fm hs hpost⟩⟩
  refine ⟨fun r hr => ?_, ret_apart hp (hfin.fr.trans (fm.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self .., hs⟩)), hmx⟩
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
    obtain hl1 : (List.map BitVec.toNat (nB s₁ ++ eB s₁)).length =
        (List.map BitVec.toNat (nB s₂ ++ eB s₂)).length := by
      simp [nB, eB, kOf, Spec.Rsa.bytesAt, h8, a0]
    obtain hl2 : (List.map BitVec.toNat (preW s₁)).length = (List.map BitVec.toNat (preW s₂)).length := by
      simp [preW, Spec.Rsa.wordsAt, a8]
    obtain ⟨h12, h3⟩ := List.append_inj hl' (by simp only [List.length_append, hl1, hl2])
    obtain ⟨h1, h2⟩ := List.append_inj h12 hl1
    obtain inj : ∀ {w : Nat} {l₁ l₂ : List (BitVec w)}, l₁.map BitVec.toNat = l₂.map BitVec.toNat → l₁ = l₂ :=
      fun h => (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 h
    obtain hne := inj h1
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

end

end

/-!
# RSAES-PKCS1-v1_5 encryption from a random tape on x86-64: the scan in constant time

Two runs from entry states that agree with an anchor `a` on the public data
(`PR`) read the same octets of the tape and keep as many of them: the scan
reads `scanLen` octets of `a`'s tape in both (`N`), each read octet is zero in
one run exactly when it is in the other, and so is each count of kept octets
(`Proof/RsaPkcs1Enc/RandomCT.lean`). So the branch on each octet, the index
of each store and the end of the loop are the same in both runs; the taint
analysis checks the rest, with these registers public.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.X86_64.Rnd

open VG VG.X86_64 VG.Impl.RsaPkcs1Enc.X86_64.Random
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

/-- An entry state meeting the precondition with the anchor's public data. -/
def PR (a s : State) : Prop := contract.pre s ∧ pub a s

theorem PR.pre {a s : State} (h : PR a s) : RPre s := pre_of h.1

theorem PR.gprEq {a s : State} (h : PR a s) {r : Reg} (hr : r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9]) :
    s.gpr r = a.gpr r := (h.2.2.1 r hr).symm

theorem PR.rspEq {a s : State} (h : PR a s) : s.gpr .rsp = a.gpr .rsp := h.2.1.symm

theorem PR.argEq {a s : State} (h : PR a s) {j : Nat} (hj : j < 9) : stackArg s j = stackArg a j :=
  (h.2.2.2.1 j hj).symm

theorem PR.fbEq {a s : State} (h : PR a s) : fb s = fb a := by
  show s.gpr .rsp - _ = a.gpr .rsp - _; rw [h.rspEq]

theorem PR.psEq {a s : State} (h : PR a s) : psLen s = psLen a := by
  unfold psLen kOf; rw [h.gprEq (r := .r8) (by decide), h.argEq (j := 2) (by decide)]

theorem PR.lenEq {a s : State} (h : PR a s) : (stackArg s 4).toNat = (stackArg a 4).toNat := by
  rw [h.argEq (by decide)]

theorem PR.traceEq {a s : State} (h : PR a s) :
    (Spec.RsaPkcs1Enc.padSearch (psLen a) (randB s)).trace =
      (Spec.RsaPkcs1Enc.padSearch (psLen a) (randB a)).trace := by
  have := h.2.2.2.2.2.2.2
  simp only [trace, h.psEq] at this
  exact this.symm

/-- The octets the scan reads, the anchor's. -/
abbrev N (a : State) : Nat := VG.Proof.RsaPkcs1Enc.scanLen (psLen a) (randB a)

theorem PR.scanEq {a s : State} (h : PR a s) :
    VG.Proof.RsaPkcs1Enc.scanLen (psLen s) (randB s) = N a := by
  rw [h.psEq]; exact VG.Proof.RsaPkcs1Enc.scanLen_eq h.traceEq

theorem PR.keptEq {a s : State} (h : PR a s) {j : Nat} (hj : j ≤ N a) :
    (kept s j).length = (kept a j).length := by
  have := VG.Proof.RsaPkcs1Enc.nz_take_length_eq h.traceEq j (by rw [← h.psEq, h.scanEq]; exact hj)
  exact this

theorem PR.zeroIff {a s : State} (h : PR a s) {j : Nat} (hj : j < N a) :
    (randB s).getD j 0 = 0 ↔ (randB a).getD j 0 = 0 :=
  VG.Proof.RsaPkcs1Enc.zero_iff h.traceEq (by rw [← h.psEq, h.scanEq]; exact hj)

/-! ## The loop -/

/-- Before octet `j` of the scan. -/
def LoopPt (p : State × Nat) (u : State) : Prop :=
  ∃ s t₀, PR p.1 s ∧ Before s t₀ ∧ At s t₀ p.2 u ∧ p.2 < (stackArg s 4).toNat ∧
    (kept s p.2).length < psLen s ∧ p.2 < N p.1

/-- After the load of octet `j`. -/
def LoadPtA (p : State × Nat) (v : State) : Prop :=
  ∃ s t₀, PR p.1 s ∧ Before s t₀ ∧ LoadPt s t₀ p.2 v ∧ p.2 < (stackArg s 4).toNat ∧
    (kept s p.2).length < psLen s ∧ p.2 < N p.1

/-- After octet `j`, before the comparison. -/
def NextPt (p : State × Nat) (w : State) : Prop :=
  ∃ s t₀, PR p.1 s ∧ Before s t₀ ∧ At s t₀ (p.2 + 1) w ∧ p.2 < N p.1

/-- After the comparison of the count with `psLen`. -/
def CmpPt (p : State × Nat) (x : State) : Prop :=
  ∃ s t₀, PR p.1 s ∧ Before s t₀ ∧ At s t₀ (p.2 + 1) x ∧ p.2 < N p.1 ∧
    x.zf = some (decide ((kept s (p.2 + 1)).length = psLen s))

theorem load_two : RelCT isa (Two LoopPt) (.block load) (Two LoadPtA) := by
  refine two_piece [.rsp, .rsi, .rcx] (fun p u₁ u₂ ⟨s₁, t₁, S₁, B₁, I₁, _⟩ ⟨s₂, t₂, S₂, B₂, I₂, _⟩ r hr => ?_)
    (by taint_decide) fun p u ⟨s, t₀, S, B, I, hi, hc, hN⟩ =>
      WP.mono (load_ok S.pre B I hi hc) fun v h => ⟨s, t₀, S, B, h, hi, hc, hN⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [(I₁.keep.gpr (by decide)).trans B₁.rsp, (I₂.keep.gpr (by decide)).trans B₂.rsp, S₁.fbEq, S₂.fbEq]
  · rw [(I₁.keep.gpr (by decide)).trans B₁.rsi, (I₂.keep.gpr (by decide)).trans B₂.rsi,
      S₁.argEq (by decide), S₂.argEq (by decide)]
  · rw [I₁.rcx, I₂.rcx]

theorem branch_two : RelCT isa (Two LoadPtA) (.ite .ne (.block keep) (.block [])) (Two NextPt) := by
  refine two_post (two_ite (fun p v₁ v₂ ⟨s₁, t₁, S₁, B₁, ⟨u₁, I₁, _, _, _, z₁, _⟩, _, _, hN₁⟩
      ⟨s₂, t₂, S₂, B₂, ⟨u₂, I₂, _, _, _, z₂, _⟩, _, _, _⟩ => ?_) ?_ ?_) ?_
  · rw [eval_ne z₁, eval_ne z₂]
    congr 2
    exact decide_eq_decide.mpr ((S₁.zeroIff hN₁).trans (S₂.zeroIff hN₁).symm)
  · refine two_taint [.rdi, .rdx] (fun p v₁ v₂ ⟨⟨s₁, t₁, S₁, B₁, ⟨u₁, I₁, _, _, _, _, k₁⟩, _, _, hN⟩, _⟩
        ⟨⟨s₂, t₂, S₂, B₂, ⟨u₂, I₂, _, _, _, _, k₂⟩, _, _, _⟩, _⟩ r hr => ?_) (by taint_decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [(k₁.gpr (by decide)).trans ((I₁.keep.gpr (by decide)).trans B₁.rdi),
        (k₂.gpr (by decide)).trans ((I₂.keep.gpr (by decide)).trans B₂.rdi), S₁.fbEq, S₂.fbEq]
    · rw [(k₁.gpr (by decide)).trans I₁.rdx, (k₂.gpr (by decide)).trans I₂.rdx,
        S₁.keptEq (Nat.le_of_lt hN), S₂.keptEq (Nat.le_of_lt hN)]
  · exact two_taint [] (fun _ _ _ _ _ r hr => absurd hr (by simp)) (by taint_decide)
  · intro p v ⟨s, t₀, S, B, L, hi, hc, hN⟩
    exact WP.mono (branch_ok S.pre B L hi hc) fun w h => ⟨s, t₀, S, B, h, hN⟩

/-- `full_ok`'s comparison, which keeps `At`. -/
theorem cmpAt_ok {s t₀ u : State} (hp : RPre s) (hb : Before s t₀) {i : Nat} (hI : At s t₀ i u) :
    WP isa (.block [.alu .cmp .rdx (.mem (sp oPs))]) u fun v => At s t₀ i v ∧
      v.zf = some (decide ((kept s i).length = psLen s)) :=
  WP.mono (full_ok hp hb hI) fun w ⟨hm, kw, hd, hzw⟩ =>
    ⟨⟨(hI.keep.trans kw).mono (by decide), hm ▸ hI.out, hm ▸ hI.buf, (kw.gpr (by decide)).trans hI.rcx,
      hd.trans hI.rdx, hI.hi, hI.hc⟩, hzw⟩

theorem cmp_two : RelCT isa (Two NextPt) (.block [.alu .cmp .rdx (.mem (sp oPs))]) (Two CmpPt) := by
  refine two_piece [.rsp] (fun p u₁ u₂ ⟨s₁, t₁, S₁, B₁, I₁, _⟩ ⟨s₂, t₂, S₂, B₂, I₂, _⟩ r hr => ?_)
    (by taint_decide) fun p u ⟨s, t₀, S, B, I, hN⟩ =>
      WP.mono (cmpAt_ok S.pre B I) fun v ⟨h, hz⟩ => ⟨s, t₀, S, B, h, hN, hz⟩
  rw [List.mem_singleton.mp hr, (I₁.keep.gpr (by decide)).trans B₁.rsp, (I₂.keep.gpr (by decide)).trans B₂.rsp,
    S₁.fbEq, S₂.fbEq]

theorem more_two : RelCT isa (Two NextPt) more fun _ _ => True := by
  refine RelCT.seq cmp_two (two_ite (fun p x₁ x₂ ⟨s₁, t₁, S₁, B₁, I₁, hN, z₁⟩ ⟨s₂, t₂, S₂, B₂, I₂, _, z₂⟩ => ?_)
    (two_taint [] (fun _ _ _ _ _ r hr => absurd hr (by simp)) (by taint_decide))
    (two_taint [] (fun _ _ _ _ _ r hr => absurd hr (by simp)) (by taint_decide)))
  rw [eval_e z₁, eval_e z₂, S₁.keptEq hN, S₂.keptEq hN, S₁.psEq, S₂.psEq]

theorem step_two : RelCT isa (Two LoopPt) step fun _ _ => True :=
  RelCT.seq load_two (RelCT.seq branch_two more_two)

/-- At the end of the scan: all `N a` octets read. -/
def ScanDone (a u : State) : Prop := ∃ s t₀, PR a s ∧ Before s t₀ ∧ At s t₀ (N a) u

theorem loop_two : RelCT isa (Two fun a s => 0 < N a ∧ LoopPt (a, 0) s) (.loop step .ne) (Two ScanDone) := by
  refine two_loop (Φ := fun a j s => LoopPt (a, j) s) N
    (step_two.mono (fun _ _ ⟨p, ⟨_, h₁⟩, ⟨_, h₂⟩⟩ => ⟨p, h₁, h₂⟩) fun _ _ h => h) ?_
  intro a j u hj ⟨s, t₀, S, B, I, hi, hc, _⟩
  change j < (stackArg s 4).toNat at hi
  change (kept s j).length < psLen s at hc
  change At s t₀ j u at I
  have hs : VG.Proof.RsaPkcs1Enc.scanLen (psLen s) (randB s) = N a := S.scanEq
  refine WP.mono (step_ok S.pre B I hi hc) fun u' ⟨I', hz⟩ => ?_
  have hst : ((kept s (j + 1)).length = psLen s ∨ j + 1 = (stackArg s 4).toNat) ↔ N a = j + 1 := by
    have := VG.Proof.RsaPkcs1Enc.stop_iff (n := psLen s) (r := randB s) (j := j) (by rw [hs]; exact hj) hc
    rw [randB_length, hs] at this; exact this
  have hk := I'.hc
  refine ⟨?_, fun hlt => ⟨s, t₀, S, B, I', ?_, ?_, hlt⟩, fun he => ⟨s, t₀, S, B, he ▸ I'⟩⟩
  · rw [eval_ne hz]
    by_cases h : (kept s (j + 1)).length = psLen s ∨ j + 1 = (stackArg s 4).toNat
    · rw [decide_eq_true h, decide_eq_false (by have := hst.mp h; omega_using [hst, h])]; rfl
    · rw [decide_eq_false h, decide_eq_true (by
        have : N a ≠ j + 1 := fun e => h (hst.mpr e)
        omega_using [hj, hst, h])]; rfl
  · show j + 1 < (stackArg s 4).toNat
    have := VG.Proof.RsaPkcs1Enc.scanLen_le (psLen s) (randB s)
    rw [randB_length, hs] at this; omega_using [hi, hst, hlt]
  · show (kept s (j + 1)).length < psLen s
    by_cases hn : (kept s (j + 1)).length = psLen s
    · have := hst.mp (.inl hn); omega_using [hst, hk, hlt]
    · omega_using [hk, hn]

theorem at_zero {s t : State} (hp : RPre s) (hcx : t.gpr .rcx = 0) (hdx : t.gpr .rdx = 0) : At s t 0 t :=
  have hP := hp.ps
  ⟨Keep.refl _ _, Outside.refl _ _ _ _, fun j hj => absurd hj (by simp [kept_zero]),
    hcx, by rw [hdx, kept_zero]; rfl, Nat.zero_le _, by rw [kept_zero]; simp⟩

/-- Before the scan. -/
def ScanPt (a t : State) : Prop :=
  ∃ s, PR a s ∧ Before s t ∧ t.gpr .rcx = 0 ∧ t.gpr .rdx = 0 ∧ t.zf = some (stackArg s 4 == 0)

theorem scan_two : RelCT isa (Two ScanPt) scan (Two ScanDone) := by
  refine two_ite (fun a t₁ t₂ ⟨s₁, S₁, _, _, _, z₁⟩ ⟨s₂, S₂, _, _, _, z₂⟩ => by
    rw [eval_ne z₁, eval_ne z₂, S₁.argEq (by decide), S₂.argEq (by decide)]) ?_ ?_
  · refine loop_two.mono (fun t₁ t₂ ⟨a, ⟨⟨s₁, S₁, B₁, c₁, d₁, z₁⟩, e₁⟩, ⟨⟨s₂, S₂, B₂, c₂, d₂, z₂⟩, _⟩⟩ => ?_)
      fun _ _ h => h
    have hl : stackArg s₁ 4 ≠ 0 := by
      intro h0; rw [eval_ne z₁, h0] at e₁; cases e₁
    have hl' : 0 < (stackArg s₁ 4).toNat := by
      rcases Nat.eq_zero_or_pos (stackArg s₁ 4).toNat with h | h
      · exact absurd (BitVec.eq_of_toNat_eq (by rw [h]; rfl)) hl
      · exact h
    have hP₁ := S₁.pre.ps
    have hP₂ := S₂.pre.ps
    have hN : 0 < N a := by
      rw [← S₁.scanEq]
      exact VG.Proof.RsaPkcs1Enc.lt_scanLen (i := 0)
        (show (kept s₁ 0).length < psLen s₁ by rw [kept_zero, List.length_nil]; omega_using [hP₁])
        (by rw [randB_length]; exact hl')
    refine ⟨a, ⟨hN, s₁, t₁, S₁, B₁, at_zero S₁.pre c₁ d₁, hl', by rw [kept_zero, List.length_nil]; omega_using [hP₁], hN⟩,
      ⟨hN, s₂, t₂, S₂, B₂, at_zero S₂.pre c₂ d₂, by rw [S₂.lenEq, ← S₁.lenEq]; exact hl',
        by rw [kept_zero, List.length_nil]; omega_using [hP₂], hN⟩⟩
  · refine two_piece [] (fun _ _ _ _ _ r hr => absurd hr (by simp)) (by taint_decide)
      fun a t ⟨⟨s, S, B, hcx, hdx, z⟩, e⟩ => WP.block_nil ⟨s, t, S, B, ?_⟩
    have h0 : stackArg s 4 = 0 := by
      rw [eval_ne z] at e
      by_cases h : stackArg s 4 = 0
      · exact h
      · rw [beq_false_of_ne h] at e; cases e
    have : N a = 0 := by
      rw [← S.scanEq]
      have := VG.Proof.RsaPkcs1Enc.scanLen_le (psLen s) (randB s)
      rw [randB_length, h0] at this
      simpa using this
    rw [this]; exact at_zero S.pre hcx hdx

end VG.Proof.RsaPkcs1Enc.X86_64.Rnd
