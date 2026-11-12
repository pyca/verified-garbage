module

public import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Time.Step
public import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.FRows
import VerifiedGarbage.Proof.Framework.RelSplit
import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Arrays
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Power
import VerifiedGarbage.Proof.Framework.Omega

-- separate module: builds in parallel with the batch's correctness (`FBatch`, `FScatter`), which
-- `FBatchRel` also waits for

/-! # A row of the fused batches in both runs

The row's loop compares `esi` with the row's end, a word of the header (`sE`), which the analysis
forgets at the loop's first store of a secret through `esi`. So the loop is related by
`RelCT.loop`: in both runs `esi` and the end are the same, by each run's frame (`RowE`), and each
of its blocks is checked by the analysis with `esi` public (`τI`), the loop's condition the same
in both runs by each run's frame. What each block needs of the masks (`MasksOk`) the row keeps.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.InvBatchRt.Time

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Rsa.X86.KeyRt VG.Impl.Rsa.X86.InvBatchRt
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Rsa.X86.KeyRt VG.Proof.Rsa.X86.InvBatchRt
open VG.Proof.Weierstrass (Unch)
open VG.Proof.Rsa.X86.InvBatchRt.F (maskW TermOk wordN_ok wordW_ok termSum acc64 acc96 advCmp_ok addEsi_ok
  topFixes_ok lastWord_ok mul_step mul_mono rowSetup_ok HdrFrame)

/-- The masks of `ms` are their coefficients' signs. -/
def MasksOk (m : Mem) (B : Addr) (ms : List Term) : Prop :=
  ∀ t ∈ ms, m.readW (off B t.m) 32 = maskW (m.readW (off B t.c) 32)

/-- Between the batch's operations: the count, and the masks `ms`. -/
def ME (B : Addr) (C : Nat → Prop) (ms : List Term) (_ : Reg → BitVec 32) (m : Mem) : Prop :=
  C (w32 m B 100) ∧ MasksOk m B ms

/-- In a row of the array at `(rv (kw len) { arr := arr })`: `esi` at `B + e`, and the row's end past its first `n` elements
of `sz` bytes. -/
def RowE (B : Addr) (C : Nat → Prop) (ms : List Term) (a0 sz n e : Nat) (g : Reg → BitVec 32) (m : Mem) : Prop :=
  C (w32 m B 100) ∧ MasksOk m B ms ∧ (g .esi).toNat = (B.toNat + e) % 2 ^ 32 ∧
    m.readW (off B sE) 32 = BitVec.ofNat 32 (B.toNat + (a0 + sz + sz * n))

/-- `τS` with `esi` public. -/
def τI (L : Lay) : VG.X86.Taint.T := { τS L with regs := .ofList [.edi, .esp, .esi] }

/-- What a row needs of its place: the array `arr` of elements of `sz` bytes, its output at byte
`o`, its terms `ts` (the signed ones `signed`), each of them among the masks `ms`, which lie
below the elements and apart from `sP` and `sE`. -/
structure RowHyp (len Z arr sz o : Nat) (ts signed ms : List Term) : Prop where
  n2 : 2 ≤ nw len
  even : nw len % 2 = 0
  hsz : sz = 16 ∨ sz = 20
  ho : o + 4 ≤ sz
  fit : rv (kw len) { arr := arr } + sz * (nw len + 2) < Z
  harr : sP + 8 ≤ rv (kw len) { arr := arr }
  hms : ∀ t ∈ ms, t.c + 4 ≤ rv (kw len) { arr := arr } ∧ t.m + 4 ≤ rv (kw len) { arr := arr } ∧
    (t.c + 4 ≤ sP ∨ sP + 8 ≤ t.c) ∧ (t.m + 4 ≤ sP ∨ sP + 8 ≤ t.m)
  hts : ∀ t ∈ ts, t ∈ ms ∧ t.x + 4 ≤ sz
  hsg : ∀ t ∈ signed, t ∈ ts

variable {L : Lay} {B : Addr} {Z len N : Nat} {args : Nat → BitVec 32} {sp : BitVec 32}

theorem agreeI {s t : State} (h : Rel L B Z len N args sp s t) (he : s.gpr .esi = t.gpr .esi) :
    VG.X86.Taint.Agree (τI L) (view s B Z) (view t B Z) := by
  have A := agreeS h
  have w₁ := A.wf₁; have w₂ := A.wf₂
  refine ⟨⟨fun r hr => ?_, A.rf.2⟩, A.wr,
    ⟨w₁.lens, w₁.bases, w₁.wbases, w₁.args, w₁.argBases, w₁.stk, w₁.frames, w₁.room⟩,
    ⟨w₂.lens, w₂.bases, w₂.wbases, w₂.args, w₂.argBases, w₂.stk, w₂.frames, w₂.room⟩, A.ok, A.slots, A.sp, A.argMem⟩
  simp only [τI, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact A.rf.1 .edi (by simp only [τS, RegSet.mem_ofList, List.mem_cons]; simp)
  · exact A.rf.1 .esp (by simp only [τS, RegSet.mem_ofList, List.mem_cons]; simp)
  · exact he

/-- `leafU`, checked from a taint `τ` that the runs agree on. -/
theorem leafT {E : (Reg → BitVec 32) → Mem → Prop} {Q : State → Prop} {c : Prog isa} (τ : VG.X86.Taint.T)
    (hA : ∀ s t, Pre L B Z len N args sp E s → Pre L B Z len N args sp E t →
      VG.X86.Taint.Agree τ (view s B Z) (view t B Z))
    (hf : ∀ s, Pre L B Z len N args sp E s → WP isa c s Q) {hc : VG.Taint.Hint VG.X86.Taint.T}
    (h : (VG.Taint.check sseTaint τ c hc).isSome = true) :
    RelCT isa (fun s t => Pre L B Z len N args sp E s ∧ Pre L B Z len N args sp E t) c (fun s t => Q s ∧ Q t) := by
  have ex : ∀ s, Pre L B Z len N args sp E s → ∃ tr z, Exec isa c (view s B Z) tr z := fun s ps =>
    let ⟨tr, z, e, _⟩ := hf _ ps.view
    ⟨tr, z, e⟩
  have R := leaf (P := fun s t => Pre L B Z len N args sp E s ∧ Pre L B Z len N args sp E t) τ
    (fun _ _ ⟨ps, pt⟩ => hA _ _ ps pt)
    (fun _ _ ⟨ps, pt⟩ => ⟨ps.1.ws.ws.workspace.wr, pt.1.ws.ws.workspace.wr⟩)
    (fun _ _ ⟨ps, pt⟩ => ⟨ex _ ps, ex _ pt⟩) h
  exact (RelCT.wp R (fun s t ⟨ps, pt⟩ => ⟨hf s ps, hf t pt⟩)).mono (fun _ _ h => h)
    (fun _ _ ⟨_, a, b⟩ => ⟨a, b⟩)

theorem unch_readW {ws : List (Nat × Nat)} {m m' : Mem} (h : Unch B ws m m') {d : Nat}
    (hd : ∀ w ∈ ws, d + 4 ≤ w.1 ∨ w.1 + w.2 ≤ d) (hd' : d + 4 ≤ 2 ^ 64) :
    m'.readW (off B d) 32 = m.readW (off B d) 32 :=
  BitVec.eq_of_toNat_eq (unch_w32 h hd hd')

/-- A step that writes only the ranges `ws`, above the header's slots and apart from the masks,
keeps the context, the call's public data, the count and the masks. -/
theorem keepE {s t : State} {rs : List Reg} {ws : List (Nat × Nat)} {ms : List Term} {C : Nat → Prop}
    (hb : Bx L s B Z len N) (hp : Public L args B Z sp s) (K : Keeps rs s t) (hedi : .edi ∉ rs) (hesp : .esp ∉ rs)
    (U : Unch B ws s.mem t.mem) (hws : ∀ w ∈ ws, 160 ≤ w.1 ∧ w.1 + w.2 ≤ Z)
    (hms : ∀ x ∈ ms, x.c + 4 ≤ Z ∧ x.m + 4 ≤ Z ∧
      ∀ w ∈ ws, (x.c + 4 ≤ w.1 ∨ w.1 + w.2 ≤ x.c) ∧ (x.m + 4 ≤ w.1 ∨ w.1 + w.2 ≤ x.m))
    (hE : ME B C ms s.gpr s.mem) : Pre L B Z len N args sp (ME B C ms) t := by
  have hn := hb.nowrap
  refine ⟨hb.keep K hedi hesp (U.outside (o := 160) (n := Z - 160) fun w hw => by have := hws w hw; omega)
      (Nat.le_refl _) (by have := hb.fits16; omega),
    hp.keep K hesp (U.outside fun w hw => by have := hws w hw; omega), ?_, fun x hx => ?_⟩
  · rw [unch_w32 U (fun w hw => .inl (by have := hws w hw; omega)) (by decide)]; exact hE.1
  · obtain ⟨hc, hm, hw⟩ := hms x hx
    rw [unch_readW U (fun w h => (hw w h).2) (by omega), unch_readW U (fun w h => (hw w h).1) (by omega)]
    exact hE.2 x hx

/-! ## Each run's frame -/

/-- A word of a row writes only its output word and `sP`. -/
theorem wordFr {s : State} {W : Addr} {bytes e sz o k y : Nat} {wide : Bool} (ws : Ws s W bytes)
    (di : PtrAt s W .edi 0) (si : PtrAt s W .esi e) {ts : List Term}
    (hts : ∀ t ∈ ts, t.c + 4 ≤ bytes ∧ t.m + 4 ≤ bytes ∧ e + (t.x + k) + 4 ≤ bytes)
    (hm : ∀ t ∈ ts, s.mem.readW (off W t.m) 32 = maskW (s.mem.readW (off W t.c) 32))
    (hy : (e + (neg sz + o + k) % 2 ^ 32) % 2 ^ 32 = y) (hyb : y + 4 ≤ bytes) (he : e < bytes)
    (hP : sP + 4 ≤ bytes) :
    WP isa (.block (wordI wide ts sz o k)) s fun u =>
      Unch W [(y, 4), (sP, 4)] s.mem u.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp] s u := by
  have ok : ∀ t ∈ ts.map (fun t => { t with x := t.x + k }), TermOk s.mem W bytes e t := by
    intro t ht
    obtain ⟨t', ht', rfl⟩ := List.mem_map.mp ht
    obtain ⟨h1, h2, h3⟩ := hts t' ht'
    exact ⟨h1, h2, by simp only; omega, hm t' ht'⟩
  have nw := ws.nowrap
  have hb := (s.gpr .ebx).isLt; have hc := (s.gpr .ecx).isLt; have hp := (s.gpr .ebp).isLt
  cases wide with
  | false =>
    refine WP.mono (wordN_ok ws di si ok hy hyb he (C := ((acc64 s : Int) + termSum s.mem W e (ts.map fun t => { t with x := t.x + k }) + 2 ^ 63) % 2 ^ 64 - 2 ^ 63 -
        termSum s.mem W e (ts.map fun t => { t with x := t.x + k }))
      (by simp only [acc64]; omega) (by omega) (by omega)) fun u ⟨mu, _, _, ku⟩ => ⟨?_, ku⟩
    rw [mu]
    exact (writeW32_outside _ _ _ (by omega)).unch.cover fun w hw => by
      simp only [List.mem_singleton] at hw; subst hw
      exact ⟨_, (List.mem_cons_self ..), Nat.le_refl _, Nat.le_refl _⟩
  | true =>
    refine WP.mono (wordW_ok ws di si ok hy hyb he hP (C := ((acc96 s : Int) + termSum s.mem W e (ts.map fun t => { t with x := t.x + k }) + 2 ^ 95) % 2 ^ 96 - 2 ^ 95 -
        termSum s.mem W e (ts.map fun t => { t with x := t.x + k }))
      (by simp only [acc96, acc64]; omega) (by omega) (by omega)) fun u ⟨mu, _, ku⟩ => ⟨?_, ku⟩
    rw [mu]
    exact (writeW32_outside _ _ _ (by omega)).unch.trans (writeW32_outside _ _ _ (by omega)).unch

variable {arr sz o : Nat} {ts signed ms : List Term} {wide : Bool} {C : Nat → Prop}

theorem RowHyp.mask (H : RowHyp len Z arr sz o ts signed ms) {m : Mem} (hm : MasksOk m B ms) :
    ∀ t ∈ ts, m.readW (off B t.m) 32 = maskW (m.readW (off B t.c) 32) :=
  fun t ht => hm t (H.hts t ht).1

/-- The masks lie apart from the row's elements and its scratch words. -/
theorem RowHyp.apart (H : RowHyp len Z arr sz o ts signed ms) {ws : List (Nat × Nat)}
    (hws : ∀ w ∈ ws, rv (kw len) { arr := arr } ≤ w.1 ∨ (sP ≤ w.1 ∧ w.1 + w.2 ≤ sP + 8)) :
    ∀ x ∈ ms, x.c + 4 ≤ Z ∧ x.m + 4 ≤ Z ∧
      ∀ w ∈ ws, (x.c + 4 ≤ w.1 ∨ w.1 + w.2 ≤ x.c) ∧ (x.m + 4 ≤ w.1 ∨ w.1 + w.2 ≤ x.m) := by
  intro x hx
  have := H.hms x hx; have := H.fit
  refine ⟨by omega, by omega, fun w hw => ?_⟩
  rcases hws w hw with h | h <;> omega

theorem rowStart_fr {s : State} (H : RowHyp len Z arr sz o ts signed ms)
    (ps : Pre L B Z len N args sp (ME B C ms) s) :
    WP isa (.block (rowStart L arr sz ++ ([.mov .ebx (.imm 0), .mov .ecx (.imm 0), .mov .ebp (.imm 0)] : List Instr) ++
      (if wide then [.store (sc sP) .ebx] else []))) s
      (Pre L B Z len N args sp (RowE B C ms (rv (kw len) { arr := arr }) sz (nw len) (rv (kw len) { arr := arr } + sz))) := by
  obtain ⟨h, hp, hE⟩ := ps
  have hn := h.nowrap
  have hZ := h.halfZ
  have hfit := H.fit; have harr := H.harr
  have eE : sE = 180 := rfl; have eP : sP = 176 := rfl
  have hA' : rv (kw len) { arr := arr, byte := sz } = rv (kw len) { arr := arr } + sz := by simp only [rv]; omega
  have scr := h.ws.ws.workspace
  have ws : Ws s B Z := ⟨scr.wr, scr.nowrap⟩
  have di : PtrAt s B .edi 0 := by rw [PtrAt, RtWs.edi_eq h.ws, BitVec.toNat_ofNat]; omega
  have m0 := mul_step (sz := sz) (show 0 < nw len + 2 by omega)
  have mfit := mul_step (sz := sz) (show nw len < nw len + 2 by omega)
  simp only [rowStart, List.append_assoc]
  refine ptr_ok h.ws h.slots hZ (r := .esi) (t := .edx) (x := { arr := arr, byte := sz }) (by decide)
    (by decide) (by decide) (by decide) (by intro e; cases e) (by rw [hA']; omega) fun u K₁ m₁ p₁ => ?_
  rw [hA'] at p₁
  have wsu := ws.of_keeps K₁
  have diu : PtrAt u B .edi 0 := by rw [PtrAt, K₁.1 _ (by decide)]; exact di
  have hh : u.mem.readW (off B halfSlot) 32 = BitVec.ofNat 32 (4 * nw len) := by
    rw [m₁, h.slots.halfW]; congr 1; have := kw_eq len; omega
  simp only [← List.append_assoc]
  refine WP.mono (rowSetup_ok (wide := wide) wsu diu p₁ hh H.hsz (by omega) (by omega)
    (by omega)) fun v ⟨_, _, _, F₀, E₀, _, K₀⟩ => ?_
  rw [m₁] at F₀
  have K : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s v := (K₁.mono (by decide)).trans (K₀.mono (by decide))
  have U : Unch B [(sP, 8)] s.mem v.mem := fun x hx => F₀ x (hx _ (List.mem_singleton_self _))
  have P := keepE (C := C) h hp K (by decide) (by decide) U (fun w hw => by
      simp only [List.mem_singleton] at hw; subst hw; dsimp only; omega)
    (H.apart fun w hw => by simp only [List.mem_singleton] at hw; subst hw; exact .inr ⟨Nat.le_refl _, Nat.le_refl _⟩) hE
  exact ⟨P.1, P.2.1, P.2.2.1, P.2.2.2, by rw [K₀.1 _ (by decide)]; exact p₁, E₀⟩

/-- Two words of the loop. -/
theorem rowPair_fr {s : State} (H : RowHyp len Z arr sz o ts signed ms) {i : Nat} (hi : 2 * i + 2 ≤ nw len)
    (ps : Pre L B Z len N args sp
      (RowE B C ms (rv (kw len) { arr := arr }) sz (nw len) (rv (kw len) { arr := arr } + sz + sz * (2 * i))) s) :
    WP isa (.block (wordI wide ts sz o 0 ++ wordI wide ts sz o sz)) s
      (Pre L B Z len N args sp
        (RowE B C ms (rv (kw len) { arr := arr }) sz (nw len) (rv (kw len) { arr := arr } + sz + sz * (2 * i)))) := by
  obtain ⟨h, hp, hC, hm, si, hE⟩ := ps
  have hn := h.nowrap
  have hfit := H.fit; have harr := H.harr; have ho := H.ho
  have eE : sE = 180 := rfl; have eP : sP = 176 := rfl
  have scr := h.ws.ws.workspace
  have ws : Ws s B Z := ⟨scr.wr, scr.nowrap⟩
  have di : PtrAt s B .edi 0 := by rw [PtrAt, RtWs.edi_eq h.ws, BitVec.toNat_ofNat]; omega
  have mi := mul_mono (sz := sz) hi
  have mn := mul_step (sz := sz) (show nw len + 1 < nw len + 2 by omega)
  have mn' := mul_step (sz := sz) (show nw len < nw len + 1 by omega)
  have hsz := H.hsz
  have e1 : sz * (2 * i + 2) = sz * (2 * i) + 2 * sz := by rw [Nat.mul_add]; omega
  rw [WP.block_append_iff]
  refine WP.mono (wordFr (k := 0) (y := (rv (kw len) { arr := arr }) + o + sz * (2 * i)) ws di si (fun t ht => by
      have := H.hms t (H.hts t ht).1; have := (H.hts t ht).2; omega) (H.mask hm)
    (by unfold neg; omega) (by omega) (by omega) (by omega)) fun u ⟨U₁, K₁⟩ => ?_
  have hB := keepE (C := C) h hp K₁ (by decide) (by decide) U₁
    (fun w hw => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hw; rcases hw with rfl | rfl <;> dsimp only <;> omega)
    (H.apart fun w hw => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · exact .inl (by dsimp only; omega)
      · exact .inr ⟨Nat.le_refl _, by dsimp only; omega⟩) ⟨hC, hm⟩
  have siu : PtrAt u B .esi ((rv (kw len) { arr := arr }) + sz + sz * (2 * i)) := by rw [PtrAt, K₁.1 _ (by decide)]; exact si
  have wsu := ws.of_keeps K₁
  have diu : PtrAt u B .edi 0 := by rw [PtrAt, K₁.1 _ (by decide)]; exact di
  have hEu : u.mem.readW (off B sE) 32 = _ := (unch_readW U₁ (fun w hw => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw; rcases hw with rfl | rfl <;> dsimp only <;> omega) (by omega)).trans hE
  refine WP.mono (wordFr (k := sz) (y := (rv (kw len) { arr := arr }) + o + sz * (2 * i) + sz) wsu diu siu (fun t ht => by
      have := H.hms t (H.hts t ht).1; have := (H.hts t ht).2; omega) (H.mask hB.2.2.2)
    (by unfold neg; omega) (by omega) (by omega) (by omega)) fun v ⟨U₂, K₂⟩ => ?_
  have hB₂ := keepE (C := C) hB.1 hB.2.1 K₂ (by decide) (by decide) U₂
    (fun w hw => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hw; rcases hw with rfl | rfl <;> dsimp only <;> omega)
    (H.apart fun w hw => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · exact .inl (by dsimp only; omega)
      · exact .inr ⟨Nat.le_refl _, by dsimp only; omega⟩) hB.2.2
  refine ⟨hB₂.1, hB₂.2.1, hB₂.2.2.1, hB₂.2.2.2, by rw [K₂.1 _ (by decide)]; exact siu, ?_⟩
  exact (unch_readW U₂ (fun w hw => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw; rcases hw with rfl | rfl <;> dsimp only <;> omega) (by omega)).trans hEu

/-- The loop's step to the next pair, and its condition. -/
theorem rowAdv_fr {s : State} (H : RowHyp len Z arr sz o ts signed ms) {i : Nat} (hi : 2 * i + 2 ≤ nw len)
    (ps : Pre L B Z len N args sp
      (RowE B C ms (rv (kw len) { arr := arr }) sz (nw len) (rv (kw len) { arr := arr } + sz + sz * (2 * i))) s) :
    WP isa (.block [.alu .add .esi (.imm (BitVec.ofNat 32 (2 * sz))), .alu .cmp .esi (.mem (sc sE))]) s fun v =>
      Pre L B Z len N args sp
        (RowE B C ms (rv (kw len) { arr := arr }) sz (nw len) (rv (kw len) { arr := arr } + sz + sz * (2 * (i + 1)))) v ∧
      isa.eval .ne v = some (!decide (2 * i + 2 = nw len)) := by
  obtain ⟨h, hp, hC, hm, si, hE⟩ := ps
  have hn := h.nowrap
  have hfit := H.fit; have harr := H.harr
  have eE : sE = 180 := rfl; have eP : sP = 176 := rfl
  have scr := h.ws.ws.workspace
  have ws : Ws s B Z := ⟨scr.wr, scr.nowrap⟩
  have di : PtrAt s B .edi 0 := by rw [PtrAt, RtWs.edi_eq h.ws, BitVec.toNat_ofNat]; omega
  have mi := mul_mono (sz := sz) hi
  have mn := mul_step (sz := sz) (show nw len + 1 < nw len + 2 by omega)
  have mn' := mul_step (sz := sz) (show nw len < nw len + 1 by omega)
  have e1 : sz * (2 * (i + 1)) = sz * (2 * i) + 2 * sz := by
    rw [show 2 * (i + 1) = 2 * i + 2 by omega, Nat.mul_add]; omega
  have e2 : sz * (2 * i + 2) = sz * (2 * i) + 2 * sz := by rw [Nat.mul_add]; omega
  refine WP.mono (advCmp_ok (d := 2 * sz) (E := rv (kw len) { arr := arr } + sz + sz * nw len) ws di si hE
    (by omega) (by omega) (by omega))
    fun w ⟨siw, mw, kw₁, ew⟩ => ⟨⟨h.keep kw₁ (by decide) (by decide) (o := 160) (c := 0)
      (by rw [mw]; exact Outside.refl _ _ _ _) (Nat.le_refl _) (by have := h.fits16; omega),
      hp.keep kw₁ (by decide) (by rw [mw]; exact Outside.refl _ _ _ _), by rw [mw]; exact hC, by rw [mw]; exact hm,
      by rw [siw, e1]; congr 1; omega, by rw [mw]; exact hE⟩, ?_⟩
  have key : rv (kw len) { arr := arr } + sz + sz * (2 * i) + 2 * sz = rv (kw len) { arr := arr } + sz + sz * nw len ↔
      2 * i + 2 = nw len :=
    ⟨fun e => Nat.eq_of_mul_eq_mul_left (show 0 < sz by have := H.hsz; omega) (by omega), fun e => by rw [← e]; omega⟩
  refine (show isa.eval .ne w = _ from ew).trans ?_
  rw [decide_eq_decide.mpr key]

/-- The row's end: word `n`, the signed terms' corrections, the last output word, `edi` again. -/
theorem rowEnd_fr {s : State} (H : RowHyp len Z arr sz o ts signed ms)
    (ps : Pre L B Z len N args sp
      (RowE B C ms (rv (kw len) { arr := arr }) sz (nw len) (rv (kw len) { arr := arr } + sz + sz * nw len)) s) :
    WP isa (.block (wordI wide ts sz o 0 ++ [.alu .add .esi (.imm (BitVec.ofNat 32 sz))] ++
        signed.flatMap (topFix wide sz) ++
        [.alu .add .ebx (.reg .ebx), .alu .add .ebx (.reg .ebx)] ++
        (if wide then [.alu .add .ebx (.mem (sc sP))] else [.alu .add .ebx (.reg .ebp)]) ++
        [.store (at_ .esi (neg sz + o)) .ebx] ++ restoreEdi L)) s
      (Pre L B Z len N args sp (ME B C ms)) := by
  obtain ⟨h, hp, hC, hm, si, hE⟩ := ps
  have hn := h.nowrap
  have hfit := H.fit; have harr := H.harr; have ho := H.ho
  have eP : sP = 176 := rfl
  have scr := h.ws.ws.workspace
  have ws : Ws s B Z := ⟨scr.wr, scr.nowrap⟩
  have di : PtrAt s B .edi 0 := by rw [PtrAt, RtWs.edi_eq h.ws, BitVec.toNat_ofNat]; omega
  have mn := mul_step (sz := sz) (show nw len + 1 < nw len + 2 by omega)
  have mn' := mul_step (sz := sz) (show nw len < nw len + 1 by omega)
  have apartW : ∀ w ∈ [((rv (kw len) { arr := arr }), sz * (nw len + 2)), (sP, 4)],
      rv (kw len) { arr := arr } ≤ w.1 ∨ (sP ≤ w.1 ∧ w.1 + w.2 ≤ sP + 8) := by
    intro w hw; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact .inl (Nat.le_refl _)
    · exact .inr ⟨Nat.le_refl _, by omega⟩
  -- The outputs' range.
  have cov : ∀ y, (rv (kw len) { arr := arr }) ≤ y → y + 4 ≤ (rv (kw len) { arr := arr }) + sz * (nw len + 2) →
      ∀ w ∈ [(y, 4), (sP, 4)], ∃ w' ∈ [((rv (kw len) { arr := arr }), sz * (nw len + 2)), (sP, 4)], w'.1 ≤ w.1 ∧ w.1 + w.2 ≤ w'.1 + w'.2 := by
    intro y h1 h2 w hw; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact ⟨_, (List.mem_cons_self ..), h1, h2⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Nat.le_refl _, Nat.le_refl _⟩
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (wordFr (k := 0) (y := (rv (kw len) { arr := arr }) + o + sz * nw len) ws di si (fun t ht => by
      have := H.hms t (H.hts t ht).1; have := (H.hts t ht).2; omega) (H.mask hm)
    (by unfold neg; omega) (by omega) (by omega) (by omega)) fun u₁ ⟨U₁, K₁⟩ => ?_
  have si₁ : PtrAt u₁ B .esi ((rv (kw len) { arr := arr }) + sz + sz * nw len) := by rw [PtrAt, K₁.1 _ (by decide)]; exact si
  rw [WP.block_append_iff]
  refine WP.mono (addEsi_ok (d := sz) si₁) fun u₂ ⟨si₂, mu₂, ku₂⟩ => ?_
  have K₂ : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u₂ := (K₁.mono (by decide)).trans (ku₂.mono (by decide))
  have hb : (rv (kw len) { arr := arr }) + sz + sz * nw len + sz = (rv (kw len) { arr := arr }) + sz * (nw len + 1) + sz := by rw [Nat.mul_succ]; omega
  rw [hb] at si₂
  have ws₂ := ws.of_keeps K₂
  have di₂ : PtrAt u₂ B .edi 0 := by rw [PtrAt, K₂.1 _ (by decide)]; exact di
  rw [WP.block_append_iff]
  refine WP.mono (topFixes_ok (wide := wide) (sz := sz) (b := (rv (kw len) { arr := arr }) + sz * (nw len + 1)) (by omega) (by omega) signed ws₂
    di₂ si₂ (fun t ht => by
      have := H.hms t (H.hts t (H.hsg t ht)).1; have := (H.hts t (H.hsg t ht)).2; omega) (by omega))
    fun u₃ ⟨_, mu₃, ku₃, _⟩ => ?_
  have K₃ := K₂.trans (ku₃.mono (by decide))
  have ws₃ := ws.of_keeps K₃
  have di₃ : PtrAt u₃ B .edi 0 := by rw [PtrAt, K₃.1 _ (by decide)]; exact di
  have si₃ : PtrAt u₃ B .esi ((rv (kw len) { arr := arr }) + sz * (nw len + 1) + sz) := by rw [PtrAt, ku₃.1 _ (by decide)]; exact si₂
  rw [show ∀ (x y z w : List Instr), x ++ (y ++ (z ++ w)) = (x ++ y ++ z) ++ w by intros; simp, WP.block_append_iff]
  refine WP.mono (lastWord_ok (o := o) (y := (rv (kw len) { arr := arr }) + o + sz * (nw len + 1)) ws₃ di₃ si₃ (by unfold neg; omega)
    (by unfold neg; omega) (by omega) (by omega) (fun _ => by omega)) fun w ⟨mw, kw₁⟩ => ?_
  have K₄ : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s w := K₃.trans (kw₁.mono (by decide))
  have U : Unch B [((rv (kw len) { arr := arr }), sz * (nw len + 2)), (sP, 4)] s.mem w.mem := by
    have U₂ : Unch B [((rv (kw len) { arr := arr }) + o + sz * (nw len + 1), 4)] u₃.mem w.mem := by
      rw [mw]; exact (writeW32_outside _ _ _ (by omega)).unch
    rw [mu₃, mu₂] at U₂
    refine ((U₁.cover (cov _ (by omega) (by omega))).trans (U₂.cover (W' := [(rv (kw len) { arr := arr }, sz * (nw len + 2)), (sP, 4)]) fun w hw => ?_)).cover fun w hw => ?_
    · simp only [List.mem_singleton] at hw; subst hw
      exact ⟨_, (List.mem_cons_self ..), by omega, by omega⟩
    · simp only [List.mem_append] at hw
      rcases hw with h | h <;> exact ⟨w, h, Nat.le_refl _, Nat.le_refl _⟩
  have O0 : Outside B 0 Z s.mem w.mem := U.outside fun w hw => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw; rcases hw with rfl | rfl <;> dsimp only <;> omega
  unfold restoreEdi
  refine wp_movS (h.ws.wsArg.keep K₄ (by decide) O0).readSrc fun t₁ V _ => WP.block_nil ?_
  have K' : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t₁ :=
    VG.Proof.Bignum.X86.PublicRt.Keeps.drop_edi (rs := [.eax, .ebx, .ecx, .edx, .ebp, .esi])
      ((K₄.mono (by decide)).trans (V.keeps.mono (by decide))) (V.gpr.trans (RtWs.edi_eq h.ws).symm)
  rw [← V.mem] at U
  exact keepE h hp K' (by decide) (by decide) U (fun w hw => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw; rcases hw with rfl | rfl <;> dsimp only <;> omega)
    (H.apart apartW) ⟨hC, hm⟩

/-! ## Both runs -/

/-- The analysis's checks of a row's blocks: its start from `τS`, the rest with `esi` public. -/
def RowChecks (L : Lay) (wide : Bool) (arr sz o : Nat) (ts signed : List Term) : Prop :=
  (∃ hc, (VG.Taint.check sseTaint (τS L) (.block (rowStart L arr sz ++
      [.mov .ebx (.imm 0), .mov .ecx (.imm 0), .mov .ebp (.imm 0)] ++
      (if wide then [.store (sc sP) .ebx] else []))) hc).isSome = true) ∧
  (∃ hc, (VG.Taint.check sseTaint (τI L) (.block (wordI wide ts sz o 0 ++ wordI wide ts sz o sz)) hc).isSome = true) ∧
  (∃ hc, (VG.Taint.check sseTaint (τI L)
      (.block [.alu .add .esi (.imm (BitVec.ofNat 32 (2 * sz))), .alu .cmp .esi (.mem (sc sE))]) hc).isSome = true) ∧
  (∃ hc, (VG.Taint.check sseTaint (τI L) (.block (wordI wide ts sz o 0 ++
      [.alu .add .esi (.imm (BitVec.ofNat 32 sz))] ++ signed.flatMap (topFix wide sz) ++
      [.alu .add .ebx (.reg .ebx), .alu .add .ebx (.reg .ebx)] ++
      (if wide then [.alu .add .ebx (.mem (sc sP))] else [.alu .add .ebx (.reg .ebp)]) ++
      [.store (at_ .esi (neg sz + o)) .ebx] ++ restoreEdi L)) hc).isSome = true)

theorem relRow (H : RowHyp len Z arr sz o ts signed ms) (hk : RowChecks L wide arr sz o ts signed) :
    RelCT isa (fun s t => Pre L B Z len N args sp (ME B C ms) s ∧ Pre L B Z len N args sp (ME B C ms) t)
      (row L wide arr sz o ts signed)
      (fun s t => Pre L B Z len N args sp (ME B C ms) s ∧ Pre L B Z len N args sp (ME B C ms) t) := by
  have he := H.even; have h2 := H.n2
  obtain ⟨⟨_, h₁⟩, ⟨_, h₂⟩, ⟨_, h₃⟩, ⟨_, h₄⟩⟩ := hk
  -- The runs agree on `esi` where each has it at the same place.
  have hAI : ∀ e s t, Pre L B Z len N args sp (RowE B C ms (rv (kw len) { arr := arr }) sz (nw len) e) s →
      Pre L B Z len N args sp (RowE B C ms (rv (kw len) { arr := arr }) sz (nw len) e) t →
      VG.X86.Taint.Agree (τI L) (view s B Z) (view t B Z) := fun _ _ _ ps pt =>
    agreeI ⟨ps.1, pt.1, ps.2.1, pt.2.1⟩ (BitVec.eq_of_toNat_eq (ps.2.2.2.2.1.trans pt.2.2.2.2.1.symm))
  unfold row
  refine RelCT.seq (leafT (τS L) (fun _ _ ps pt => agreeS ⟨ps.1, pt.1, ps.2.1, pt.2.1⟩)
    (fun s ps => rowStart_fr (wide := wide) H ps) h₁) (RelCT.seq ?_
      (leafT (τI L) (hAI _) (fun s ps => rowEnd_fr H ps) h₄))
  -- The loop: `i` pairs of words done, `n / 2 - i` to go.
  let I : Nat → Nat → State → State → Prop := fun k i s t => (k = nw len / 2 - i ∧ 2 * i < nw len) ∧
    Pre L B Z len N args sp (RowE B C ms (rv (kw len) { arr := arr }) sz (nw len)
      (rv (kw len) { arr := arr } + sz + sz * (2 * i))) s ∧
    Pre L B Z len N args sp (RowE B C ms (rv (kw len) { arr := arr }) sz (nw len)
      (rv (kw len) { arr := arr } + sz + sz * (2 * i))) t
  refine (RelCT.loop (fun k s t => ∃ i, I k i s t) (fun k => RelCT.exists_ fun i => ?_) (nw len / 2)).mono
    (fun s t ⟨ps, pt⟩ => ⟨0, ⟨by omega, by omega⟩, by rw [show sz * (2 * 0) = 0 by simp, Nat.add_zero]; exact ps,
      by rw [show sz * (2 * 0) = 0 by simp, Nat.add_zero]; exact pt⟩)
    (fun _ _ h => h)
  by_cases hi : k = nw len / 2 - i ∧ 2 * i < nw len
  swap
  · exact RelCT.of_false fun _ _ h => hi h.1
  have hi2 : 2 * i + 2 ≤ nw len := by omega
  unfold rowStep
  refine (RelCT.block_append (RelCT.seq
      (leafT (τI L) (hAI _) (fun s ps => rowPair_fr (wide := wide) H hi2 ps) h₂)
      (leafT (τI L) (hAI _) (fun s ps => rowAdv_fr H hi2 ps) h₃))).mono (fun _ _ h => ⟨h.2.1, h.2.2⟩)
    fun s t ⟨⟨ps, es⟩, ⟨pt, et⟩⟩ => ⟨by rw [es, et], fun hx => ?_, fun hx => ⟨k - 1, by omega, i + 1, ⟨by omega, ?_⟩, ps, pt⟩⟩
  · rw [es] at hx
    have hn : 2 * i + 2 = nw len := by simpa using hx
    rw [show 2 * (i + 1) = nw len by omega] at ps pt
    exact ⟨ps, pt⟩
  · rw [es] at hx
    have : 2 * i + 2 ≠ nw len := by simpa using hx
    omega

end VG.Proof.Rsa.X86.InvBatchRt.Time
