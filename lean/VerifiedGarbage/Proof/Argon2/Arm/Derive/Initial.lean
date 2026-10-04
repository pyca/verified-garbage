import VerifiedGarbage.Proof.Argon2.Arm.Derive.Scratch
import VerifiedGarbage.Proof.Argon2.Initial

/-!
# Argon2 on ARMv7: H₀

`HI s₀ data s`: the BLAKE2b state at `scratch` has absorbed `data`, whose
length is in the locals. `start_ok` absorbs the header, `absorb_ok` an
input with its length prefix, `finish_ok` writes the digest to the first 64
bytes of the locals: `code_ok`, H₀ (`Spec.Argon2.initialHash`).
-/

namespace VG.Proof.Argon2.Arm.Derive

open VG VG.Arm
open VG.Proof.MdStream.Arm (Upd Mupd wp_mov wp_add wp_ldr wp_str op2_imm op2_reg)
open VG.Proof.Blake2.Arm.Stream (wp_adds wp_adc)
open VG.Spec.Blake2 (Repr b bytesAt)
open VG.Proof.Argon2.Arm.HPrime (Ctx Keeps)
open VG.Impl.Argon2.Arm.Derive (countLoOff countHiOff argOff ld st)

/-- H₀'s streaming state at `scratch`, with `data` absorbed. -/
structure HI (s₀ : State) (data : List Byte) (s : State) : Prop where
  inv : Inv s₀ s
  prm : Prm s₀ s
  r4 : s.gpr .r4 = scrP s₀
  repr : Repr b (Spec.Blake2.init b 64 0) s.mem (State.addr (scrP s₀)) data
  lo : lw s₀ s countLoOff = BitVec.ofNat 32 data.length
  hi : lw s₀ s countHiOff = BitVec.ofNat 32 (data.length / 2 ^ 32)
  len : data.length < 2 ^ 36

theorem Prm.of_lw {s₀ s t : State} (pr : Prm s₀ s)
    (h : ∀ d ∈ [Impl.Argon2.Arm.Derive.divisorOff, Impl.Argon2.Arm.Derive.segLenOff,
      Impl.Argon2.Arm.Derive.laneLenOff, Impl.Argon2.Arm.Derive.strideOff], lw s₀ t d = lw s₀ s d) :
    Prm s₀ t :=
  ⟨by rw [h _ (by simp)]; exact pr.divisor, by rw [h _ (by simp)]; exact pr.segLen,
    by rw [h _ (by simp)]; exact pr.laneLen, by rw [h _ (by simp)]; exact pr.stride⟩

/-- The parameters are kept when the locals at the offsets of `prmOk` are. -/
theorem prm_offs : ∀ d ∈ [Impl.Argon2.Arm.Derive.divisorOff, Impl.Argon2.Arm.Derive.segLenOff,
    Impl.Argon2.Arm.Derive.laneLenOff, Impl.Argon2.Arm.Derive.strideOff],
    d + 4 ≤ 144 ∧ 72 ≤ d ∧ (d + 4 ≤ countLoOff ∨ countHiOff + 4 ≤ d) := by decide

section
variable {s₀ : State} (hp : DPre s₀)
include hp

theorem scr_addr {o : Nat} (ho : o < 16384) :
    State.addr (scrP s₀ + BitVec.ofNat 32 o) = State.addr (scrP s₀) + BitVec.ofNat 64 o :=
  addr_add (by have := hp.scr_fits; omega)

/-- `str r, [r4, #o]`, to `scratch`. -/
theorem wp_stscr {s : State} (h : Inv s₀ s) (hb : s.gpr .r4 = scrP s₀) {o : Nat} (ho : o + 4 ≤ 4096)
    {r : Reg} {is : List Instr} {Q : State → Prop}
    (k : ∀ t, Inv s₀ t → t.mem = s.mem.writeW (State.addr (scrP s₀) + BitVec.ofNat 64 o) (s.gpr r) →
      t.gpr = s.gpr → (∀ d, d + 4 ≤ 144 → lw s₀ t d = lw s₀ s d) →
      Frame [⟨State.addr (scrP s₀) + BitVec.ofNat 64 o, 4⟩] s.mem t.mem → WP isa (.block is) t Q) :
    WP isa (.block (.str r .r4 o :: is)) s Q := by
  have hc : (scrR s₀).Contains (State.addr (scrP s₀) + BitVec.ofNat 64 o) 4 :=
    Offset.contains_base _ (by omega) (by omega)
  refine wp_str (by omega) (by rw [hb, scr_addr hp (by omega)]) (by rw [h.wr]; exact ⟨scrR s₀, scr_mem hp, hc⟩)
    fun t u => ?_
  have f : Frame [⟨State.addr (scrP s₀) + BitVec.ofNat 64 o, 4⟩] s.mem t.mem := by
    rw [u.mem]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine k t (h.step u.sp (by rw [u.gpr]) u.rd u.wr ?_) u.mem u.gpr
    (fun d hd => lw_keep hp f (fun r hr => ?_) hd) f
  · rw [u.mem]; exact (Frame.refl _ _).writeW (r := scrR s₀) (by simp) _ hc
  · simp only [List.mem_singleton] at hr; subst hr
    exact ⟨scrR s₀, by simp, scr_sub (by omega)⟩

omit hp in
/-- A store to `scratch` from offset 192 on keeps the streaming state. -/
theorem repr_store {m m' : Mem} {o : Nat} (ho : 192 ≤ o) (ho' : o + 4 ≤ 16384)
    (f : Frame [⟨State.addr (scrP s₀) + BitVec.ofNat 64 o, 4⟩] m m') {data : List Byte}
    (h : Repr b (Spec.Blake2.init b 64 0) m (State.addr (scrP s₀)) data) :
    Repr b (Spec.Blake2.init b 64 0) m' (State.addr (scrP s₀)) data :=
  HPrime.repr_frame f (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.base_disjoint _ ho (by omega)) h

end

/-- The bytes at `p`: a word, then the rest. -/
theorem bytes_word (m : Mem) (p : Addr) (n : Nat) :
    bytesAt m p (4 + n) = Spec.Blake2.wordBytes (m.readW p 32) ++ bytesAt m (p + BitVec.ofNat 64 4) n := by
  rw [Proof.Blake2.bytesAt_add, Proof.Blake2.wordBytes_readW (w := 32) m p (.inl rfl)]

theorem variant_code {s₀ : State} (hk : (kindV s₀).toNat ≤ 2) : (prm s₀).variant.code = (kindV s₀).toNat := by
  simp only [prm]
  rcases (by omega : (kindV s₀).toNat = 0 ∨ (kindV s₀).toNat = 1 ∨ (kindV s₀).toNat = 2) with h | h | h <;>
    simp [h, Spec.Argon2.Variant.code, Spec.Argon2.params]

theorem le32_arg (x : BitVec 32) : Spec.Argon2.le32 x.toNat = Spec.Blake2.wordBytes x := by
  simp only [Spec.Argon2.le32, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem header_eq : Impl.Argon2.Arm.Derive.header =
    [ld .r0 (argOff 7), .str .r0 .r4 768,
     ld .r0 (argOff 17), .str .r0 .r4 772,
     ld .r0 (argOff 6), .str .r0 .r4 776,
     ld .r0 (argOff 5), .str .r0 .r4 780,
     .mov .r0 (.imm 0x13), .str .r0 .r4 784,
     ld .r0 (argOff 0), .str .r0 .r4 788] := rfl

section
variable {s₀ : State} (hp : DPre s₀)
include hp

omit hp in
/-- A word of `scratch` is kept by a store to another one. -/
theorem scr_keep {m m' : Mem} {o o' : Nat} (ho : o + 4 ≤ 16384) (ho' : o' + 4 ≤ 16384)
    (hd : o + 4 ≤ o' ∨ o' + 4 ≤ o)
    (f : Frame [⟨State.addr (scrP s₀) + BitVec.ofNat 64 o', 4⟩] m m') :
    m'.readW (State.addr (scrP s₀) + BitVec.ofNat 64 o) 32 = m.readW (State.addr (scrP s₀) + BitVec.ofNat 64 o) 32 := by
  refine f.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_singleton] at hr; subst hr
  exact Offset.disjoint _ hd (by omega) (by omega)

/-- The six header words, at `scratch + 768`. -/
theorem header_ok {s : State} (h : Inv s₀ s) (pr : Prm s₀ s) (hb : s.gpr .r4 = scrP s₀)
    (repr : Repr b (Spec.Blake2.init b 64 0) s.mem (State.addr (scrP s₀)) []) :
    WP isa (.block Impl.Argon2.Arm.Derive.header) s fun t => Inv s₀ t ∧ Prm s₀ t ∧
      t.gpr .r4 = scrP s₀ ∧ Repr b (Spec.Blake2.init b 64 0) t.mem (State.addr (scrP s₀)) [] ∧
      bytesAt t.mem (State.addr (scrP s₀) + BitVec.ofNat 64 768) 24 = Proof.Argon2.initialHeader (prm s₀) ∧
      ∀ d, d + 4 ≤ 144 → lw s₀ t d = lw s₀ s d := by
  rw [header_eq]
  refine wp_ldarg hp h (i := 7) (by decide) fun s₁ u₁ => ?_
  have i₁ := h.upd u₁ (by decide)
  have b₁ : s₁.gpr .r4 = scrP s₀ := by rw [u₁.other _ (by decide), hb]
  refine wp_stscr hp i₁ b₁ (o := 768) (by decide) fun s₂ i₂ m₂ g₂ l₂ f₂ => ?_
  have b₂ : s₂.gpr .r4 = scrP s₀ := by rw [g₂, b₁]
  refine wp_ldarg hp i₂ (i := 17) (by decide) fun s₃ u₃ => ?_
  have i₃ := i₂.upd u₃ (by decide)
  have b₃ : s₃.gpr .r4 = scrP s₀ := by rw [u₃.other _ (by decide), b₂]
  refine wp_stscr hp i₃ b₃ (o := 772) (by decide) fun s₄ i₄ m₄ g₄ l₄ f₄ => ?_
  have b₄ : s₄.gpr .r4 = scrP s₀ := by rw [g₄, b₃]
  refine wp_ldarg hp i₄ (i := 6) (by decide) fun s₅ u₅ => ?_
  have i₅ := i₄.upd u₅ (by decide)
  have b₅ : s₅.gpr .r4 = scrP s₀ := by rw [u₅.other _ (by decide), b₄]
  refine wp_stscr hp i₅ b₅ (o := 776) (by decide) fun s₆ i₆ m₆ g₆ l₆ f₆ => ?_
  have b₆ : s₆.gpr .r4 = scrP s₀ := by rw [g₆, b₅]
  refine wp_ldarg hp i₆ (i := 5) (by decide) fun s₇ u₇ => ?_
  have i₇ := i₆.upd u₇ (by decide)
  have b₇ : s₇.gpr .r4 = scrP s₀ := by rw [u₇.other _ (by decide), b₆]
  refine wp_stscr hp i₇ b₇ (o := 780) (by decide) fun s₈ i₈ m₈ g₈ l₈ f₈ => ?_
  have b₈ : s₈.gpr .r4 = scrP s₀ := by rw [g₈, b₇]
  refine wp_mov (op2_imm (by decide)) fun s₉ u₉ => ?_
  have i₉ := i₈.upd u₉ (by decide)
  have b₉ : s₉.gpr .r4 = scrP s₀ := by rw [u₉.other _ (by decide), b₈]
  refine wp_stscr hp i₉ b₉ (o := 784) (by decide) fun s₁₀ i₁₀ m₁₀ g₁₀ l₁₀ f₁₀ => ?_
  have b₁₀ : s₁₀.gpr .r4 = scrP s₀ := by rw [g₁₀, b₉]
  refine wp_ldarg hp i₁₀ (i := 0) (by decide) fun s₁₁ u₁₁ => ?_
  have i₁₁ := i₁₀.upd u₁₁ (by decide)
  have b₁₁ : s₁₁.gpr .r4 = scrP s₀ := by rw [u₁₁.other _ (by decide), b₁₀]
  refine wp_stscr hp i₁₁ b₁₁ (o := 788) (by decide) fun t it mt gt lt ft => WP.block_nil ?_
  -- The locals.
  have L : ∀ d, d + 4 ≤ 144 → lw s₀ t d = lw s₀ s d := fun d hd => by
    rw [lt d hd, lw_mem u₁₁.mem, l₁₀ d hd, lw_mem u₉.mem, l₈ d hd, lw_mem u₇.mem, l₆ d hd, lw_mem u₅.mem,
      l₄ d hd, lw_mem u₃.mem, l₂ d hd, lw_mem u₁.mem]
  -- The streaming state.
  have R : Repr b (Spec.Blake2.init b 64 0) t.mem (State.addr (scrP s₀)) [] := by
    refine repr_store (by decide) (by decide) ft ?_
    rw [u₁₁.mem]; refine repr_store (by decide) (by decide) f₁₀ ?_
    rw [u₉.mem]; refine repr_store (by decide) (by decide) f₈ ?_
    rw [u₇.mem]; refine repr_store (by decide) (by decide) f₆ ?_
    rw [u₅.mem]; refine repr_store (by decide) (by decide) f₄ ?_
    rw [u₃.mem]; refine repr_store (by decide) (by decide) f₂ ?_
    rw [u₁.mem]; exact repr
  refine ⟨it, ⟨?_, ?_, ?_, ?_⟩, by rw [gt, b₁₁], R, ?_, L⟩
  · rw [L _ (by decide)]; exact pr.divisor
  · rw [L _ (by decide)]; exact pr.segLen
  · rw [L _ (by decide)]; exact pr.laneLen
  · rw [L _ (by decide)]; exact pr.stride
  -- The words.
  have w0 : t.mem.readW (State.addr (scrP s₀) + BitVec.ofNat 64 768) 32 = arg s₀ 7 := by
    rw [scr_keep (by decide) (by decide) (by decide) ft, u₁₁.mem,
      scr_keep (by decide) (by decide) (by decide) f₁₀, u₉.mem,
      scr_keep (by decide) (by decide) (by decide) f₈, u₇.mem,
      scr_keep (by decide) (by decide) (by decide) f₆, u₅.mem,
      scr_keep (by decide) (by decide) (by decide) f₄, u₃.mem, m₂, Mem.readW_writeW_self32, u₁.gpr]
  have w1 : t.mem.readW (State.addr (scrP s₀) + BitVec.ofNat 64 772) 32 = arg s₀ 17 := by
    rw [scr_keep (by decide) (by decide) (by decide) ft, u₁₁.mem,
      scr_keep (by decide) (by decide) (by decide) f₁₀, u₉.mem,
      scr_keep (by decide) (by decide) (by decide) f₈, u₇.mem,
      scr_keep (by decide) (by decide) (by decide) f₆, u₅.mem, m₄, Mem.readW_writeW_self32, u₃.gpr]
  have w2 : t.mem.readW (State.addr (scrP s₀) + BitVec.ofNat 64 776) 32 = arg s₀ 6 := by
    rw [scr_keep (by decide) (by decide) (by decide) ft, u₁₁.mem,
      scr_keep (by decide) (by decide) (by decide) f₁₀, u₉.mem,
      scr_keep (by decide) (by decide) (by decide) f₈, u₇.mem, m₆, Mem.readW_writeW_self32, u₅.gpr]
  have w3 : t.mem.readW (State.addr (scrP s₀) + BitVec.ofNat 64 780) 32 = arg s₀ 5 := by
    rw [scr_keep (by decide) (by decide) (by decide) ft, u₁₁.mem,
      scr_keep (by decide) (by decide) (by decide) f₁₀, u₉.mem, m₈, Mem.readW_writeW_self32, u₇.gpr]
  have w4 : t.mem.readW (State.addr (scrP s₀) + BitVec.ofNat 64 784) 32 = 0x13 := by
    rw [scr_keep (by decide) (by decide) (by decide) ft, u₁₁.mem, m₁₀, Mem.readW_writeW_self32, u₉.gpr]
  have w5 : t.mem.readW (State.addr (scrP s₀) + BitVec.ofNat 64 788) 32 = arg s₀ 0 := by
    rw [mt, Mem.readW_writeW_self32, u₁₁.gpr]
  have step : ∀ o, State.addr (scrP s₀) + BitVec.ofNat 64 o + BitVec.ofNat 64 4 =
      State.addr (scrP s₀) + BitVec.ofNat 64 (o + 4) := fun o => by
    rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  rw [show (24 : Nat) = 4 + 20 from rfl, bytes_word, step, show (20 : Nat) = 4 + 16 from rfl, bytes_word, step,
    show (16 : Nat) = 4 + 12 from rfl, bytes_word, step, show (12 : Nat) = 4 + 8 from rfl, bytes_word, step,
    show (8 : Nat) = 4 + 4 from rfl, bytes_word, step, show (4 : Nat) = 4 + 0 from rfl, bytes_word]
  simp only [Nat.reduceAdd]
  rw [w0, w1, w2, w3, w4, w5]
  simp only [Proof.Argon2.initialHeader, prm, ← le32_arg, List.append_assoc,
    bytesAt, List.range_zero, List.map_nil, List.append_nil]
  have vc := variant_code hp.kind_le
  simp only [prm] at vc
  rw [vc]
  rfl

/-- `n` bytes of `scratch` at offset `d` are writable. -/
theorem scr_cov {s : State} (h : Inv s₀ s) {d n : Nat} (hd : d + n ≤ 16384) :
    Covers [⟨State.addr (scrP s₀) + BitVec.ofNat 64 d, n⟩] s.wr := by
  rw [h.wr]
  exact Covers.of_sub (rs' := [scrR s₀]) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scrR s₀, List.mem_singleton_self _, d, rfl, hd⟩) |>.trans
    fun a n ⟨r, hr, hc⟩ => ⟨r, by simp only [List.mem_singleton] at hr; subst hr; exact scr_mem hp, hc⟩

/-- The stack below the locals is outside `scratch`. -/
theorem stk_scr {d n k : Nat} (hd : d + n ≤ 16384) (hk : k ≤ 40) :
    (stkR (E s₀) k).Disjoint ⟨State.addr (scrP s₀) + BitVec.ofNat 64 d, n⟩ :=
  ((hp.stk_all (scrR s₀) (by simp)).sub_left fun a ha =>
    call_stk hp a (VG.Proof.Argon2.Arm.stkR_sub hk (by rw [E_nat hp]; have := hp.sp_lo; omega) a ha)).sub_right
    (scr_sub hd)

/-- A store to the locals keeps the streaming state at `scratch`. -/
theorem repr_loc {m : Mem} {d : Nat} (hd : d + 4 ≤ 144) (v : BitVec 32) {h0 : Spec.Blake2.HashValue 64}
    {data : List Byte} (h : Repr b h0 m (State.addr (scrP s₀)) data) :
    Repr b h0 (m.writeW (State.addr (E s₀ + BitVec.ofNat 32 d)) v) (State.addr (scrP s₀)) data :=
  HPrime.repr_frame ((Frame.refl [⟨State.addr (E s₀ + BitVec.ofNat 32 d), 4⟩] m).writeW
    (List.mem_singleton_self _) v (Region.contains_self _ _)) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ((loc_disj hp hd (scrR s₀) (by simp)).symm).sub_left (scr_sub (d := 0) (n := 192) (by decide) |>
        fun hs => by simpa using hs)) h

/-- `start`'s first block: `r4 :=` `scratch`, and the digest length. -/
theorem stA_ok {s : State} (h : Inv s₀ s) (pr : Prm s₀ s) :
    WP isa (.block [ld .r4 (argOff 15), .mov .r1 (.imm 64)]) s fun t =>
      Inv s₀ t ∧ Prm s₀ t ∧ t.gpr .r4 = scrP s₀ ∧ t.gpr .r1 = BitVec.ofNat 32 64 := by
  refine wp_ldarg hp h (i := 15) (by decide) fun s₁ u₁ => wp_mov (op2_imm (by decide)) fun s₂ u₂ =>
    WP.block_nil ?_
  have e : ∀ d, lw s₀ s₂ d = lw s₀ s d := fun d => by rw [lw_mem u₂.mem, lw_mem u₁.mem]
  exact ⟨(h.upd u₁ (by decide)).upd u₂ (by decide),
    ⟨by rw [e]; exact pr.divisor, by rw [e]; exact pr.segLen, by rw [e]; exact pr.laneLen, by rw [e]; exact pr.stride⟩,
    by rw [u₂.other _ (by decide), u₁.gpr], by rw [u₂.gpr]; rfl⟩

/-- `start`'s `init`. -/
theorem stInit_ok {s : State}
    (h : Inv s₀ s ∧ Prm s₀ s ∧ s.gpr .r4 = scrP s₀ ∧ s.gpr .r1 = BitVec.ofNat 32 64) :
    WP isa Impl.Argon2.Arm.HPrime.init s fun t => Inv s₀ t ∧ Prm s₀ t ∧ t.gpr .r4 = scrP s₀ ∧
      Repr b (Spec.Blake2.init b 64 0) t.mem (State.addr (scrP s₀)) [] :=
  (init_k (ctx hp h.1 h.2.2.1) (n := 64) h.2.2.2 (by decide) (by decide)).mono fun _ ⟨r, k⟩ =>
    let ⟨i, l⟩ := h.1.keeps hp k
    ⟨i, Prm.of_lw h.2.1 fun d hd => l d (prm_offs d hd).1, (k.gpr _ (by decide)).trans h.2.2.1, r⟩

/-- `start`'s hash of the header. -/
theorem stFix_ok {s : State}
    (h : Inv s₀ s ∧ Prm s₀ s ∧ s.gpr .r4 = scrP s₀ ∧
      Repr b (Spec.Blake2.init b 64 0) s.mem (State.addr (scrP s₀)) [] ∧
      bytesAt s.mem (State.addr (scrP s₀) + BitVec.ofNat 64 768) 24 = Proof.Argon2.initialHeader (prm s₀)) :
    WP isa (Impl.Argon2.Arm.HPrime.absorbFixed 768 24) s fun t => Inv s₀ t ∧ Prm s₀ t ∧
      t.gpr .r4 = scrP s₀ ∧
      Repr b (Spec.Blake2.init b 64 0) t.mem (State.addr (scrP s₀)) (Proof.Argon2.initialHeader (prm s₀)) := by
  have hs := hp.scr_fits
  obtain ⟨i₄, pr₄, b₄, r₄, hd₄⟩ := h
  refine (HPrime.absorbFixed_ok (ctx hp i₄ b₄) (offset := 768) (size := 24) (by decide) (by decide) (by omega)
    (by decide) (by decide) (by decide) (scr_cov hp i₄ (by decide)) (stk_scr hp (by decide) (by decide)) r₄).mono
    fun s₅ ⟨r₅, k₅⟩ => ?_
  rw [hd₄] at r₅
  obtain ⟨i₅, l₅⟩ := i₄.keeps hp k₅
  exact ⟨i₅, Prm.of_lw pr₄ fun d hd => l₅ d (prm_offs d hd).1, (k₅.gpr _ (by decide)).trans b₄, r₅⟩

/-- `start`'s count of the header's bytes. -/
theorem stCnt_ok {s : State}
    (h : Inv s₀ s ∧ Prm s₀ s ∧ s.gpr .r4 = scrP s₀ ∧
      Repr b (Spec.Blake2.init b 64 0) s.mem (State.addr (scrP s₀)) (Proof.Argon2.initialHeader (prm s₀))) :
    WP isa (.block [.mov .r0 (.imm 24), st countLoOff .r0, .mov .r0 (.imm 0), st countHiOff .r0]) s
      (HI s₀ (Proof.Argon2.initialHeader (prm s₀))) := by
  obtain ⟨i₅, pr₄, b₅, r₅⟩ := h
  refine wp_mov (op2_imm (by decide)) fun s₆ u₆ => ?_
  have i₆ := i₅.upd u₆ (by decide)
  refine wp_stloc hp i₆ (d := countLoOff) (by decide) fun s₇ i₇ v₇ o₇ g₇ m₇ => ?_
  refine wp_mov (op2_imm (by decide)) fun s₈ u₈ => ?_
  have i₈ := i₇.upd u₈ (by decide)
  refine wp_stloc hp i₈ (d := countHiOff) (by decide) fun t it vt ot gt mt => WP.block_nil ?_
  have L : ∀ d, d + 4 ≤ 144 → (d + 4 ≤ countLoOff ∨ countHiOff + 4 ≤ d) → lw s₀ t d = lw s₀ s d :=
    fun d hd hd' => by
      rw [ot d (by omega) (by simp only [countHiOff, countLoOff] at hd' ⊢; omega), lw_mem u₈.mem,
        o₇ d (by omega) (by simp only [countHiOff, countLoOff] at hd' ⊢; omega), lw_mem u₆.mem]
  refine ⟨it, Prm.of_lw pr₄ fun d hd => L d (prm_offs d hd).1 (prm_offs d hd).2.2, ?_, ?_, ?_, ?_, ?_⟩
  · rw [gt, u₈.other _ (by decide), g₇, u₆.other _ (by decide), b₅]
  · rw [mt, u₈.mem, m₇, u₆.mem]
    exact repr_loc hp (by decide) _ (repr_loc hp (by decide) _ r₅)
  · rw [ot _ (by decide) (by decide), lw_mem u₈.mem, v₇, u₆.gpr, Proof.Argon2.initialHeader_length]; rfl
  · rw [vt, u₈.gpr, Proof.Argon2.initialHeader_length]; rfl
  · rw [Proof.Argon2.initialHeader_length]; decide

theorem start_ok {s : State} (h : Inv s₀ s) (pr : Prm s₀ s) :
    WP isa Impl.Argon2.Arm.Derive.start s (HI s₀ (Proof.Argon2.initialHeader (prm s₀))) := by
  unfold Impl.Argon2.Arm.Derive.start
  refine WP.seq ((stA_ok hp h pr).mono fun s₂ h₂ => WP.seq ((stInit_ok hp h₂).mono fun s₃ ⟨i₃, pr₃, b₃, r₃⟩ =>
    WP.seq ((header_ok hp i₃ pr₃ b₃ r₃).mono fun s₄ ⟨i₄, pr₄, b₄, r₄, hd₄, _⟩ =>
      WP.seq ((stFix_ok hp ⟨i₄, pr₄, b₄, r₄, hd₄⟩).mono fun s₅ h₅ => stCnt_ok hp h₅))))

end

/-- The carry into the high word of a count. -/
theorem carry_pair {c x : Nat} (_hc : c < 2 ^ 36) (hx : x < 2 ^ 32) :
    BitVec.ofNat 32 (c / 2 ^ 32) + 0 +
      (if decide (2 ^ 32 ≤ (BitVec.ofNat 32 c).toNat + (BitVec.ofNat 32 x).toNat) = true then 1 else 0) =
    BitVec.ofNat 32 ((c + x) / 2 ^ 32) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat (w := 32) (x := c), BitVec.toNat_ofNat (w := 32) (x := x), Nat.mod_eq_of_lt hx]
  by_cases h : 2 ^ 32 ≤ c % 2 ^ 32 + x
  · simp [h, BitVec.toNat_add] <;> omega
  · simp [h] <;> omega

theorem count64 {n : Nat} (h : n < 2 ^ 64) :
    BitVec.ofNat 32 (n / 2 ^ 32) ++ BitVec.ofNat 32 n = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  rw [Proof.Blake2.Arm.Stream.toNat_append32, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- `addCount`: the 64-bit count in the locals, `c`, plus `x`. -/
theorem count_ok {s : State} (h : Inv s₀ s) {c x : Nat} (hc : c < 2 ^ 36) (hx : x < 2 ^ 32)
    (lo : lw s₀ s countLoOff = BitVec.ofNat 32 c) (hi : lw s₀ s countHiOff = BitVec.ofNat 32 (c / 2 ^ 32))
    {y : Op2} (hy : ∀ t : State, (∀ r, r ≠ .r2 → r ≠ .r3 → t.gpr r = s.gpr r) →
      y.eval t = some (BitVec.ofNat 32 x))
    {is : List Instr} {Q : State → Prop}
    (k : ∀ t, Inv s₀ t → lw s₀ t countLoOff = BitVec.ofNat 32 (c + x) →
      lw s₀ t countHiOff = BitVec.ofNat 32 ((c + x) / 2 ^ 32) →
      (∀ e, e + 4 ≤ 256 → (e + 4 ≤ countLoOff ∨ countHiOff + 4 ≤ e) → lw s₀ t e = lw s₀ s e) →
      (∀ r, r ≠ .r2 → r ≠ .r3 → t.gpr r = s.gpr r) →
      t.mem = (s.mem.writeW (State.addr (E s₀ + BitVec.ofNat 32 countLoOff)) (BitVec.ofNat 32 (c + x))).writeW
        (State.addr (E s₀ + BitVec.ofNat 32 countHiOff)) (BitVec.ofNat 32 ((c + x) / 2 ^ 32)) →
      t.gpr .r2 = BitVec.ofNat 32 (c + x) → t.gpr .r3 = BitVec.ofNat 32 ((c + x) / 2 ^ 32) →
      WP isa (.block is) t Q) :
    WP isa (.block (Impl.Argon2.Arm.Derive.addCount y ++ is)) s Q := by
  simp only [Impl.Argon2.Arm.Derive.addCount, List.cons_append, List.nil_append]
  refine wp_ldloc hp h (d := countLoOff) (by decide) fun s₁ u₁ => ?_
  have i₁ := h.upd u₁ (by decide)
  refine wp_ldloc hp i₁ (d := countHiOff) (by decide) fun s₂ u₂ => ?_
  have i₂ := i₁.upd u₂ (by decide)
  have m₂ : s₂.mem = s.mem := by rw [u₂.mem, u₁.mem]
  have o₂ : ∀ r, r ≠ .r2 → r ≠ .r3 → s₂.gpr r = s.gpr r := fun r a b => by rw [u₂.other _ b, u₁.other _ a]
  refine wp_adds (hy s₂ o₂) fun s₃ u₃ c₃ => ?_
  have i₃ := i₂.upd u₃ (by decide)
  refine wp_adc (op2_imm (by decide)) fun s₄ u₄ _ => ?_
  have i₄ := i₃.upd u₄ (by decide)
  have e₁ : s₂.gpr .r2 = BitVec.ofNat 32 c := by rw [u₂.other _ (by decide), u₁.gpr, lo]
  have vlo : s₄.gpr .r2 = BitVec.ofNat 32 (c + x) := by
    rw [u₄.other _ (by decide), u₃.gpr, e₁, BitVec.ofNat_add]
  have vhi : s₄.gpr .r3 = BitVec.ofNat 32 ((c + x) / 2 ^ 32) := by
    rw [u₄.gpr, c₃, u₃.other _ (by decide), u₂.gpr, lw_mem u₁.mem, hi, e₁]
    exact carry_pair hc hx
  refine wp_stloc hp i₄ (d := countLoOff) (by decide) fun s₅ i₅ v₅ o₅ g₅ m₅ => ?_
  refine wp_stloc hp i₅ (d := countHiOff) (by decide) fun t it vt ot gt mt => k t it ?_ ?_ ?_ ?_ ?_
    (by rw [gt, g₅, vlo]) (by rw [gt, g₅, vhi])
  · rw [ot _ (by decide) (by decide), v₅, vlo]
  · rw [vt, g₅, vhi]
  · intro e he hd
    rw [ot e he (by simp only [countHiOff, countLoOff] at hd ⊢; omega),
      o₅ e he (by simp only [countHiOff, countLoOff] at hd ⊢; omega), lw_mem u₄.mem, lw_mem u₃.mem,
      lw_mem m₂]
  · intro r h1 h2
    rw [gt, g₅, u₄.other _ h2, u₃.other _ h1, o₂ r h1 h2]
  · rw [mt, m₅, g₅, vhi, vlo, u₄.mem, u₃.mem, m₂]

end

/-- H₀'s streaming state at `scratch`, with `data` absorbed and the count `c` in
the locals. -/
structure HC (s₀ : State) (data : List Byte) (c : Nat) (s : State) : Prop where
  inv : Inv s₀ s
  prm : Prm s₀ s
  r4 : s.gpr .r4 = scrP s₀
  repr : Repr b (Spec.Blake2.init b 64 0) s.mem (State.addr (scrP s₀)) data
  lo : lw s₀ s countLoOff = BitVec.ofNat 32 c
  hi : lw s₀ s countHiOff = BitVec.ofNat 32 (c / 2 ^ 32)

theorem HI.hc {s₀ s : State} {data : List Byte} (h : HI s₀ data s) : HC s₀ data data.length s :=
  ⟨h.inv, h.prm, h.r4, h.repr, h.lo, h.hi⟩

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- `absorb`'s first block: LE32 of the length at `scratch + 792`, and `update`'s arguments. -/
theorem absA_ok {len : Nat} (hlen : len < 18) {data : List Byte} {c : Nat} {s : State} (h : HC s₀ data c s) :
    WP isa (.block [ld .r0 (argOff len), .str .r0 .r4 792, ld .r2 countLoOff, ld .r3 countHiOff,
      .dp .add .r9 .r4 (.imm 792), .mov .r10 (.imm 4)]) s fun t =>
      HC s₀ data c t ∧ t.gpr .r9 = scrP s₀ + 792 ∧ (t.gpr .r10).toNat = 4 ∧ t.gpr .r2 = BitVec.ofNat 32 c ∧
      t.gpr .r3 = BitVec.ofNat 32 (c / 2 ^ 32) ∧
      bytesAt t.mem (State.addr (scrP s₀ + 792)) 4 = Spec.Argon2.le32 (arg s₀ len).toNat := by
  have hs := hp.scr_fits
  refine wp_ldarg hp h.inv (i := len) hlen fun s₁ u₁ => ?_
  have i₁ := h.inv.upd u₁ (by decide)
  have b₁ : s₁.gpr .r4 = scrP s₀ := by rw [u₁.other _ (by decide), h.r4]
  refine wp_stscr hp i₁ b₁ (o := 792) (by decide) fun s₂ i₂ m₂ g₂ l₂ f₂ => ?_
  refine wp_ldloc hp i₂ (d := countLoOff) (by decide) fun s₃ u₃ => ?_
  refine wp_ldloc hp (i₂.upd u₃ (by decide)) (d := countHiOff) (by decide) fun s₄ u₄ => ?_
  refine wp_add (op2_imm (by decide)) fun s₅ u₅ => wp_mov (op2_imm (by decide)) fun s₆ u₆ => WP.block_nil ?_
  have i₆ := (((i₂.upd u₃ (by decide)).upd u₄ (by decide)).upd u₅ (by decide)).upd u₆ (by decide)
  have m₆ : s₆.mem = s₂.mem := by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem]
  have L₂ : ∀ d, d + 4 ≤ 144 → lw s₀ s₂ d = lw s₀ s d := fun d hd => by rw [l₂ d hd, lw_mem u₁.mem]
  have L₆ : ∀ d, d + 4 ≤ 144 → lw s₀ s₆ d = lw s₀ s d := fun d hd => by rw [lw_mem m₆, L₂ d hd]
  have e792 : State.addr (scrP s₀ + 792) = State.addr (scrP s₀) + BitVec.ofNat 64 792 :=
    scr_addr hp (o := 792) (by decide)
  have r4₄ : s₄.gpr .r4 = scrP s₀ := by rw [u₄.other _ (by decide), u₃.other _ (by decide), g₂, b₁]
  refine ⟨⟨i₆, Prm.of_lw h.prm fun d hd => L₆ d (prm_offs d hd).1,
    by rw [u₆.other _ (by decide), u₅.other _ (by decide), r4₄],
    by rw [m₆]; exact repr_store (by decide) (by decide) f₂ (by rw [u₁.mem]; exact h.repr),
    by rw [L₆ _ (by decide)]; exact h.lo, by rw [L₆ _ (by decide)]; exact h.hi⟩, ?_, by rw [u₆.gpr]; rfl, ?_, ?_, ?_⟩
  · rw [u₆.other _ (by decide), u₅.gpr, r4₄]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, L₂ _ (by decide), h.lo]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, lw_mem u₃.mem, L₂ _ (by decide), h.hi]
  · rw [e792, show (4 : Nat) = 4 + 0 from rfl, bytes_word, m₆, m₂, Mem.readW_writeW_self32, u₁.gpr, le32_arg]
    rfl

/-- `absorb`'s first `update`: LE32 of the length. -/
theorem absU1_ok {len : Nat} {data : List Byte} {c : Nat} {s : State} (h : HC s₀ data c s)
    (hd : data.length = c) (hc : c + 4 < 2 ^ 36) (r9 : s.gpr .r9 = scrP s₀ + 792) (r10 : (s.gpr .r10).toNat = 4)
    (r2 : s.gpr .r2 = BitVec.ofNat 32 c) (r3 : s.gpr .r3 = BitVec.ofNat 32 (c / 2 ^ 32))
    (w : bytesAt s.mem (State.addr (scrP s₀ + 792)) 4 = Spec.Argon2.le32 (arg s₀ len).toNat) :
    WP isa Impl.Argon2.Arm.HPrime.update s (HC s₀ (data ++ Spec.Argon2.le32 (arg s₀ len).toNat) c) := by
  have hs := hp.scr_fits
  have e792 : State.addr (scrP s₀ + 792) = State.addr (scrP s₀) + BitVec.ofNat 64 792 :=
    scr_addr hp (o := 792) (by decide)
  refine (update_k (ctx hp h.inv h.r4) (D := scrP s₀ + 792) (L := 4) r9 r10
    (by have : (scrP s₀ + 792).toNat = (scrP s₀).toNat + 792 := add_nat (k := 792) (by omega)
        omega)
    (by rw [e792]; exact Covers.right (scr_cov hp h.inv (by decide)))
    (by rw [e792]; exact Offset.disjoint_base _ (by decide) (by decide))
    (by rw [e792]; exact stk_scr hp (by decide) (by decide)) h.repr
    (by rw [r3, r2, hd]; exact count64 (by omega)) (by omega)).mono fun t ⟨r, k⟩ => ?_
  obtain ⟨i, l⟩ := h.inv.keeps hp k
  rw [w] at r
  exact ⟨i, Prm.of_lw h.prm fun d hd => l d (prm_offs d hd).1,
    (k.gpr _ (by decide)).trans h.r4, r, by rw [l _ (by decide)]; exact h.lo, by rw [l _ (by decide)]; exact h.hi⟩

/-- `absorb`'s second block: the count advanced by 4, and `update`'s arguments. -/
theorem absB_ok {ptr len : Nat} (hptr : ptr < 18) (hlen : len < 18) {data : List Byte} {c : Nat}
    (hc : c < 2 ^ 36) {s : State} (h : HC s₀ data c s) :
    WP isa (.block (Impl.Argon2.Arm.Derive.addCount (.imm 4) ++
      ([ld .r9 (argOff ptr), ld .r10 (argOff len)] : List Instr)))
      s fun t => HC s₀ data (c + 4) t ∧ t.gpr .r9 = arg s₀ ptr ∧ (t.gpr .r10).toNat = (arg s₀ len).toNat ∧
        t.gpr .r2 = BitVec.ofNat 32 (c + 4) ∧ t.gpr .r3 = BitVec.ofNat 32 ((c + 4) / 2 ^ 32) := by
  refine count_ok hp h.inv (x := 4) hc (by decide) h.lo h.hi (fun _ _ => op2_imm (by decide))
    fun s₉ i₉ lo₉ hi₉ o₉ g₉ m₉ c₉ d₉ => wp_ldarg hp i₉ (i := ptr) hptr fun s₁₀ u₁₀ =>
      wp_ldarg hp (i₉.upd u₁₀ (by decide)) (i := len) hlen fun s₁₁ u₁₁ => WP.block_nil ?_
  have i₁₁ := (i₉.upd u₁₀ (by decide)).upd u₁₁ (by decide)
  have m₁₁ : s₁₁.mem = s₉.mem := by rw [u₁₁.mem, u₁₀.mem]
  refine ⟨⟨i₁₁, Prm.of_lw h.prm fun d hd => ?_, ?_, ?_, by rw [lw_mem m₁₁]; exact lo₉, by rw [lw_mem m₁₁]; exact hi₉⟩,
    by rw [u₁₁.other _ (by decide), u₁₀.gpr], by rw [u₁₁.gpr],
    by rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), c₉],
    by rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), d₉]⟩
  · rw [lw_mem m₁₁, o₉ d (by have := (prm_offs d hd).1; omega) (prm_offs d hd).2.2]
  · rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), g₉ _ (by decide) (by decide), h.r4]
  · rw [m₁₁, m₉]; exact repr_loc hp (by decide) _ (repr_loc hp (by decide) _ h.repr)

/-- `absorb`'s second `update`: the input. -/
theorem absU2_ok {ptr len : Nat}
    (hR : (⟨State.addr (arg s₀ ptr), (arg s₀ len).toNat⟩ : Region) ∈ [pwR s₀, saltR s₀, secR s₀, adR s₀])
    (hfit : (arg s₀ ptr).toNat + (arg s₀ len).toNat ≤ 2 ^ 32) {data : List Byte} {c : Nat} {s : State}
    (h : HC s₀ data c s) (hd : data.length = c) (hc : c + 2 ^ 32 < 2 ^ 36) (r9 : s.gpr .r9 = arg s₀ ptr)
    (r10 : (s.gpr .r10).toNat = (arg s₀ len).toNat) (r2 : s.gpr .r2 = BitVec.ofNat 32 c)
    (r3 : s.gpr .r3 = BitVec.ofNat 32 (c / 2 ^ 32)) :
    WP isa Impl.Argon2.Arm.HPrime.update s
      (HC s₀ (data ++ bytesAt s₀.mem (State.addr (arg s₀ ptr)) (arg s₀ len).toNat) c) := by
  have hlt := (arg s₀ len).isLt
  have hR' : (⟨State.addr (arg s₀ ptr), (arg s₀ len).toNat⟩ : Region) ∈
      [pwR s₀, saltR s₀, secR s₀, adR s₀, argR s₀] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR ⊢
    rcases hR with h | h | h | h <;> simp [h]
  have hS : (⟨State.addr (arg s₀ ptr), (arg s₀ len).toNat⟩ : Region) ∈
      [pwR s₀, saltR s₀, secR s₀, adR s₀, memR s₀, scrR s₀, outR s₀] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR ⊢
    rcases hR with h | h | h | h <;> simp [h]
  have rin := hp.ro_w _ hR' (scrR s₀) (by simp)
  refine (update_k (ctx hp h.inv h.r4) (D := arg s₀ ptr) (L := (arg s₀ len).toNat) r9 r10 hfit
    (by rw [h.inv.rd, hp.rd]
        exact Covers.of_sub fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact ⟨_, List.mem_append_left _ hR', 0, by simp, by simp⟩)
    (rin.sub_right (Region.sub_prefix (by decide)))
    ((hp.stk_all _ hS).sub_left fun a ha => call_stk hp a (stk32_call hp a ha))
    h.repr (by rw [r3, r2, hd]; exact count64 (by omega)) (by omega)).mono fun t ⟨r, k⟩ => ?_
  obtain ⟨i, l⟩ := h.inv.keeps hp k
  have inp : bytesAt s.mem (State.addr (arg s₀ ptr)) (arg s₀ len).toNat =
      bytesAt s₀.mem (State.addr (arg s₀ ptr)) (arg s₀ len).toNat :=
    h.inv.input hp (R := ⟨State.addr (arg s₀ ptr), (arg s₀ len).toNat⟩) hR
  rw [inp] at r
  exact ⟨i, Prm.of_lw h.prm fun d hd => l d (prm_offs d hd).1,
    (k.gpr _ (by decide)).trans h.r4, r, by rw [l _ (by decide)]; exact h.lo, by rw [l _ (by decide)]; exact h.hi⟩

/-- `absorb`'s last block: the count advanced by the input's length. -/
theorem absC_ok {len : Nat} (hlen : len < 18) {data : List Byte} {c : Nat} (hc : c < 2 ^ 36) {s : State}
    (h : HC s₀ data c s) :
    WP isa (.block (ld .r0 (argOff len) :: Impl.Argon2.Arm.Derive.addCount (.reg .r0))) s
      (HC s₀ data (c + (arg s₀ len).toNat)) := by
  refine wp_ldarg hp h.inv (i := len) hlen fun s₁ u₁ => ?_
  have i₁ := h.inv.upd u₁ (by decide)
  rw [← List.append_nil (Impl.Argon2.Arm.Derive.addCount _)]
  refine count_ok hp i₁ (x := (arg s₀ len).toNat) hc (arg s₀ len).isLt (by rw [lw_mem u₁.mem]; exact h.lo)
    (by rw [lw_mem u₁.mem]; exact h.hi)
    (fun t ht => by rw [op2_reg, ht _ (by decide) (by decide), u₁.gpr, BitVec.ofNat_toNat, BitVec.setWidth_eq])
    fun t it lo hi o g mt _ _ => WP.block_nil ⟨it, Prm.of_lw h.prm fun d hd => ?_, ?_, ?_, lo, hi⟩
  · rw [o d (by have := (prm_offs d hd).1; omega) (prm_offs d hd).2.2, lw_mem u₁.mem]
  · rw [g _ (by decide) (by decide), u₁.other _ (by decide), h.r4]
  · rw [mt, u₁.mem]; exact repr_loc hp (by decide) _ (repr_loc hp (by decide) _ h.repr)

theorem absorb_ok {ptr len : Nat} (hptr : ptr < 18) (hlen : len < 18)
    (hR : (⟨State.addr (arg s₀ ptr), (arg s₀ len).toNat⟩ : Region) ∈ [pwR s₀, saltR s₀, secR s₀, adR s₀])
    (hfit : (arg s₀ ptr).toNat + (arg s₀ len).toNat ≤ 2 ^ 32) {data : List Byte}
    (hd : data.length + 4 + 2 ^ 32 < 2 ^ 36) {s : State} (h : HI s₀ data s) :
    WP isa (Impl.Argon2.Arm.Derive.absorb ptr len) s
      (HI s₀ (Proof.Argon2.appendInput data (bytesAt s₀.mem (State.addr (arg s₀ ptr)) (arg s₀ len).toNat))) := by
  have hlt := (arg s₀ len).isLt
  unfold Impl.Argon2.Arm.Derive.absorb
  refine WP.seq ((absA_ok hp hlen h.hc).mono fun s₁ ⟨h₁, e₁, d₁, c₁, x₁, w₁⟩ => ?_)
  refine WP.seq ((absU1_ok hp h₁ rfl (by omega) e₁ d₁ c₁ x₁ w₁).mono fun s₂ h₂ => ?_)
  refine WP.seq ((absB_ok hp hptr hlen (by omega) h₂).mono fun s₃ ⟨h₃, e₃, d₃, c₃, x₃⟩ => ?_)
  refine WP.seq ((absU2_ok hp hR hfit h₃ (by simp [Proof.Argon2.le32_length]) (by omega) e₃ d₃ c₃ x₃).mono
    fun s₄ h₄ => ?_)
  refine (absC_ok hp hlen (by omega) h₄).mono fun t ht => ?_
  have hd' : Proof.Argon2.appendInput data (bytesAt s₀.mem (State.addr (arg s₀ ptr)) (arg s₀ len).toNat) =
      data ++ Spec.Argon2.le32 (arg s₀ len).toNat ++
        bytesAt s₀.mem (State.addr (arg s₀ ptr)) (arg s₀ len).toNat := by
    simp only [Proof.Argon2.appendInput, bytesAt, List.length_map, List.length_range]
  have hl : (Proof.Argon2.appendInput data (bytesAt s₀.mem (State.addr (arg s₀ ptr)) (arg s₀ len).toNat)).length =
      data.length + 4 + (arg s₀ len).toNat := by
    rw [Proof.Argon2.appendInput_length]; simp only [bytesAt, List.length_map, List.length_range]
  refine ⟨ht.inv, ht.prm, ht.r4, by rw [hd']; exact ht.repr, by rw [hl]; exact ht.lo, by rw [hl]; exact ht.hi,
    by rw [hl]; omega⟩

end

/-- The bytes of `4 k` bytes, from their words. -/
theorem bytes_of_words {m m' : Mem} {p p' : Addr} {k : Nat}
    (h : ∀ j < k, m'.readW (p' + BitVec.ofNat 64 (4 * j)) 32 = m.readW (p + BitVec.ofNat 64 (4 * j)) 32) :
    bytesAt m' p' (4 * k) = bytesAt m p (4 * k) := by
  rw [Proof.Blake2.bytesAt_words (w := 32), Proof.Blake2.bytesAt_words (w := 32)]
  simp only [List.flatMap]
  refine congrArg List.flatten (List.map_congr_left fun j hj => ?_)
  rw [← Proof.Blake2.wordBytes_readW (w := 32) _ _ (.inl rfl), ← Proof.Blake2.wordBytes_readW (w := 32) _ _ (.inl rfl)]
  exact congrArg _ (h j (List.mem_range.mp hj))

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- A store to the locals keeps `scratch`. -/
theorem scr_loc {m : Mem} {d o : Nat} (hd : d + 4 ≤ 144) (ho : o + 4 ≤ 16384) (v : BitVec 32) :
    (m.writeW (State.addr (E s₀ + BitVec.ofNat 32 d)) v).readW (State.addr (scrP s₀) + BitVec.ofNat 64 o) 32 =
      m.readW (State.addr (scrP s₀) + BitVec.ofNat 64 o) 32 := by
  refine ((Frame.refl [⟨State.addr (E s₀ + BitVec.ofNat 32 d), 4⟩] m).writeW (List.mem_singleton_self _) v
    (Region.contains_self _ _)).readW (r := ⟨State.addr (scrP s₀) + BitVec.ofNat 64 o, 4⟩)
    (Region.contains_self _ _) ?_ (by decide)
  intro r hr
  simp only [List.mem_singleton] at hr; subst hr
  exact ((loc_disj hp hd (scrR s₀) (by simp)).symm.sub_left (scr_sub ho))

/-- The first `k` words of the digest, copied to the locals. -/
theorem copy_ok {s : State} (h : Inv s₀ s) (hb : s.gpr .r4 = scrP s₀) :
    ∀ k ≤ 16, WP isa (.block ((List.range k).flatMap Impl.Argon2.Arm.Derive.copyWord)) s fun t =>
      Inv s₀ t ∧ t.gpr .r4 = scrP s₀ ∧
      (∀ j < k, lw s₀ t (4 * j) = s.mem.readW (State.addr (scrP s₀) + BitVec.ofNat 64 (768 + 4 * j)) 32) ∧
      (∀ o, o + 4 ≤ 16384 → t.mem.readW (State.addr (scrP s₀) + BitVec.ofNat 64 o) 32 =
        s.mem.readW (State.addr (scrP s₀) + BitVec.ofNat 64 o) 32) ∧
      (∀ e, e + 4 ≤ 256 → 4 * k ≤ e → lw s₀ t e = lw s₀ s e)
  | 0, _ => WP.block_nil ⟨h, hb, fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ => rfl, fun _ _ _ => rfl⟩
  | k + 1, hk => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine WP.block_append ((copy_ok h hb k (by omega)).mono fun t ⟨it, bt, wt, st, lt⟩ => ?_)
    simp only [Impl.Argon2.Arm.Derive.copyWord]
    refine wp_ldr (by omega) (by rw [bt, scr_addr hp (by omega)]) (by
        rw [it.rd, it.wr]
        exact ⟨scrR s₀, List.mem_append_right _ (scr_mem hp), Offset.contains_base _ (by omega) (by omega)⟩)
      fun t₁ u₁ => ?_
    have i₁ := it.upd u₁ (by decide)
    refine wp_stloc hp i₁ (d := 4 * k) (by omega) fun t₂ i₂ v₂ o₂ g₂ m₂ => WP.block_nil
      ⟨i₂, by rw [g₂, u₁.other _ (by decide), bt], fun j hj => ?_, fun o ho => ?_, fun e he hke => ?_⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · rw [o₂ _ (by omega) (by omega), lw_mem u₁.mem]; exact wt j hj
      · rw [v₂, u₁.gpr, st _ (by omega)]
    · rw [m₂, scr_loc hp (by omega) ho, u₁.mem]; exact st o ho
    · rw [o₂ _ he (by omega), lw_mem u₁.mem]; exact lt e he (by omega)

/-- `finish`'s first block: the count, for `finalize`. -/
theorem fiA_ok {data : List Byte} {s : State} (h : HI s₀ data s) :
    WP isa (.block [ld .r2 countLoOff, ld .r3 countHiOff]) s fun t => HI s₀ data t ∧
      t.gpr .r2 = BitVec.ofNat 32 data.length ∧ t.gpr .r3 = BitVec.ofNat 32 (data.length / 2 ^ 32) := by
  refine wp_ldloc hp h.inv (d := countLoOff) (by decide) fun s₁ u₁ =>
    wp_ldloc hp (h.inv.upd u₁ (by decide)) (d := countHiOff) (by decide) fun s₂ u₂ =>
      WP.block_nil ?_
  have m₂ : s₂.mem = s.mem := by rw [u₂.mem, u₁.mem]
  refine ⟨⟨(h.inv.upd u₁ (by decide)).upd u₂ (by decide), Prm.of_lw h.prm fun d _ => lw_mem m₂ d,
    by rw [u₂.other _ (by decide), u₁.other _ (by decide), h.r4], by rw [m₂]; exact h.repr,
    by rw [lw_mem m₂]; exact h.lo, by rw [lw_mem m₂]; exact h.hi, h.len⟩,
    by rw [u₂.other _ (by decide), u₁.gpr, h.lo], by rw [u₂.gpr, lw_mem u₁.mem, h.hi]⟩

/-- `finish`'s `finalize`: the digest at `scratch + 768`. -/
theorem fiFin_ok {data : List Byte} {s : State} (h : HI s₀ data s)
    (r2 : s.gpr .r2 = BitVec.ofNat 32 data.length) (r3 : s.gpr .r3 = BitVec.ofNat 32 (data.length / 2 ^ 32)) :
    WP isa Impl.Argon2.Arm.HPrime.finalize s fun t => Inv s₀ t ∧ Prm s₀ t ∧ t.gpr .r4 = scrP s₀ ∧
      bytesAt t.mem (State.addr (scrP s₀) + 768) 64 = Spec.Blake2.finalHash b (Spec.Blake2.init b 64 0) data := by
  have hn := h.len
  refine (finalize_k (ctx hp h.inv h.r4) (h0 := Spec.Blake2.init b 64 0) h.repr
    (by rw [r3, r2]; exact count64 (by omega)) (by omega)).mono fun s₃ ⟨dg, k₃⟩ => ?_
  obtain ⟨i₃, l₃⟩ := h.inv.keeps hp k₃
  exact ⟨i₃, Prm.of_lw h.prm fun d hd => l₃ d (prm_offs d hd).1, (k₃.gpr _ (by decide)).trans h.r4, dg⟩

/-- `finish`'s copy of the digest to the locals. -/
theorem fiCopy_ok {s : State} {dg : List Byte} (h : Inv s₀ s ∧ Prm s₀ s ∧ s.gpr .r4 = scrP s₀ ∧
      bytesAt s.mem (State.addr (scrP s₀) + 768) 64 = dg) :
    WP isa (.block ((List.range 16).flatMap Impl.Argon2.Arm.Derive.copyWord)) s fun t => Inv s₀ t ∧ Prm s₀ t ∧
      bytesAt t.mem (State.addr (E s₀)) 64 = dg := by
  have hs := hp.scr_fits
  have hE := E_hi hp
  obtain ⟨i₃, pr₃, b₃, dg₃⟩ := h
  refine (copy_ok hp i₃ b₃ 16 (Nat.le_refl _)).mono fun t ⟨it, _, wt, _, lt⟩ =>
    ⟨it, Prm.of_lw pr₃ fun d hd => ?_, ?_⟩
  · rw [lt d (by have := (prm_offs d hd).1; omega) (by have := (prm_offs d hd).2.1; omega)]
  · rw [← dg₃]
    refine bytes_of_words (k := 16) fun j hj => ?_
    have := wt j hj
    simp only [lw] at this
    rw [loc_addr hp (by omega)] at this
    rw [this, BitVec.add_assoc, show (768 : Addr) = BitVec.ofNat 64 768 from rfl, BitVec.ofNat_add_ofNat]

theorem finish_ok {data : List Byte} {s : State} (h : HI s₀ data s) :
    WP isa Impl.Argon2.Arm.Derive.finish s fun t => Inv s₀ t ∧ Prm s₀ t ∧
      bytesAt t.mem (State.addr (E s₀)) 64 = Spec.Blake2.finalHash b (Spec.Blake2.init b 64 0) data := by
  unfold Impl.Argon2.Arm.Derive.finish
  exact WP.seq ((fiA_ok hp h).mono fun s₂ ⟨h₂, c₂, d₂⟩ => WP.seq ((fiFin_ok hp h₂ c₂ d₂).mono
    fun s₃ h₃ => fiCopy_ok hp h₃))

theorem code_ok {s : State} (h : Inv s₀ s) (pr : Prm s₀ s) :
    WP isa Impl.Argon2.Arm.Derive.code s fun t => Inv s₀ t ∧ Prm s₀ t ∧
      bytesAt t.mem (State.addr (E s₀)) 64 =
        Spec.Argon2.initialHash (prm s₀) (pwB s₀) (saltB s₀) (secB s₀) (adB s₀) := by
  have l1 := (arg s₀ 2).isLt
  have l2 := (arg s₀ 4).isLt
  have l3 := (arg s₀ 10).isLt
  unfold Impl.Argon2.Arm.Derive.code
  refine WP.seq ((start_ok hp h pr).mono fun s₁ h₁ => ?_)
  refine WP.seq ((absorb_ok hp (ptr := 1) (len := 2) (by decide) (by decide) (by simp) hp.pw_fits
    (by rw [Proof.Argon2.initialHeader_length]; omega) h₁).mono fun s₂ h₂ => ?_)
  refine WP.seq ((absorb_ok hp (ptr := 3) (len := 4) (by decide) (by decide) (by simp) hp.salt_fits
    (by simp only [Proof.Argon2.appendInput_length, Proof.Argon2.initialHeader_length, bytesAt,
      List.length_map, List.length_range]; omega) h₂).mono fun s₃ h₃ => ?_)
  refine WP.seq ((absorb_ok hp (ptr := 9) (len := 10) (by decide) (by decide) (by simp) hp.sec_fits
    (by simp only [Proof.Argon2.appendInput_length, Proof.Argon2.initialHeader_length, bytesAt,
      List.length_map, List.length_range]; omega) h₃).mono fun s₄ h₄ => ?_)
  refine WP.seq ((absorb_ok hp (ptr := 11) (len := 12) (by decide) (by decide) (by simp) hp.ad_fits
    (by simp only [Proof.Argon2.appendInput_length, Proof.Argon2.initialHeader_length, bytesAt,
      List.length_map, List.length_range]; omega) h₄).mono fun s₅ h₅ => ?_)
  refine (finish_ok hp h₅).mono fun t ⟨it, pt, bt⟩ => ⟨it, pt, ?_⟩
  rw [bt, Proof.Argon2.initialHash_stream, List.take_of_length_le (by rw [HPrime.finalHash_length])]
  rfl

end

end VG.Proof.Argon2.Arm.Derive
