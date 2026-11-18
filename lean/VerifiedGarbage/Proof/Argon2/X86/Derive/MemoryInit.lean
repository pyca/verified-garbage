module

public import VerifiedGarbage.Proof.Argon2.MemoryInit
public import VerifiedGarbage.Proof.Argon2.Matrix
public import VerifiedGarbage.Proof.Argon2.X86.Derive.Scratch
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Argon2.X86.Compress
public import VerifiedGarbage.Proof.Argon2.Contract
public import VerifiedGarbage.Proof.Argon2.X86.HPrime.Calls
public import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Argon2.X86.HPrime.Verified
import VerifiedGarbage.Proof.Argon2.X86.CompressLit
import VerifiedGarbage.Proof.Blake2.X86.Blake2b
import VerifiedGarbage.Proof.Blake2.X86.LitB
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TacticTemplate
import VerifiedGarbage.Proof.Sha256.X86.Lit
public import VerifiedGarbage.Proof.Argon2.Initial
import VerifiedGarbage.Proof.Argon2.X86.HPrime.Finish
import VerifiedGarbage.Proof.Blake2.X86.Stream.Common
import VerifiedGarbage.Proof.Blake2.X86.Stream.Verified

/-! ### `Argon2.X86.Derive.Initial`, which this module and modules that import it used -/

section

/-!
# Argon2 on x86 (32-bit): H₀

`HI s₀ data s`: the BLAKE2b state at `scratch` has absorbed `data`, whose
length is in the locals. `start_ok` absorbs the header, `absorb_ok` an
input with its length prefix, `finish_ok` writes the digest to the first 64
bytes of the locals: `code_ok`, H₀ (`Spec.Argon2.initialHash`).
-/

@[expose] public section

namespace VG.Proof.Argon2.X86.Derive

open VG VG.X86
open VG.X86.Wp (Upd Mupd wp_movi wp_mov wp_add wp_addi)
open VG.Spec.Blake2 (Repr b bytesAt)
open VG.Proof.Argon2.X86.HPrime (Ctx Keeps)
open VG.Impl.Argon2.X86.Derive (countLoOff countHiOff argOff)

/-- H₀'s streaming state at `scratch`, with `data` absorbed. -/
structure HI (s₀ : State) (data : List Byte) (s : State) : Prop where
  inv : Inv s₀ s
  prm : Prm s₀ s
  ebx : s.gpr .ebx = scrP s₀
  repr : Repr b (Spec.Blake2.init b 64 0) s.mem ((scrP s₀).setWidth 64) data
  lo : lw s₀ s countLoOff = BitVec.ofNat 32 data.length
  hi : lw s₀ s countHiOff = BitVec.ofNat 32 (data.length / 2 ^ 32)
  len : data.length < 2 ^ 36

theorem Prm.of_lw {s₀ s t : State} (pr : Prm s₀ s)
    (h : ∀ d ∈ [Impl.Argon2.X86.Derive.divisorOff, Impl.Argon2.X86.Derive.segLenOff,
      Impl.Argon2.X86.Derive.laneLenOff, Impl.Argon2.X86.Derive.strideOff], lw s₀ t d = lw s₀ s d) :
    Prm s₀ t :=
  ⟨by rw [h _ (by simp)]; exact pr.divisor, by rw [h _ (by simp)]; exact pr.segLen,
    by rw [h _ (by simp)]; exact pr.laneLen, by rw [h _ (by simp)]; exact pr.stride⟩

section
variable {s₀ : State} (hp : DPre s₀)
include hp

theorem scr_addr {o : Nat} (ho : o < 16384) :
    addr (scrP s₀) o = (scrP s₀).setWidth 64 + BitVec.ofNat 64 o :=
  addr_eq (by have := hp.scr_fits; omega_arith)

/-- `mov [ebx + o], r`, to `scratch`. -/
theorem wp_stscr {s : State} (h : Inv s₀ s) (hb : s.gpr .ebx = scrP s₀) {o : Nat} (ho : o + 4 ≤ 16384)
    {r : Reg} {is : List Instr} {Q : State → Prop}
    (k : ∀ t, Inv s₀ t → t.mem = s.mem.writeW (addr (scrP s₀) o) (s.gpr r) → t.gpr = s.gpr →
      (∀ d, d + 4 ≤ 144 → lw s₀ t d = lw s₀ s d) →
      Frame [⟨(scrP s₀).setWidth 64 + BitVec.ofNat 64 o, 4⟩] s.mem t.mem → WP isa (.block is) t Q) :
    WP isa (.block (.store ⟨.ebx, o⟩ r :: is)) s Q := by
  obtain hc : (scrR s₀).Contains (addr (scrP s₀) o) 4 := by
    rw [scr_addr hp (by omega_arith)]; exact Offset.contains_base _ ho (by omega_arith)
  refine VG.X86.Wp.wp_stm hb (by rw [h.wr]; exact ⟨scrR s₀, scr_mem hp, hc⟩) fun t u => ?_
  obtain f : Frame [⟨(scrP s₀).setWidth 64 + BitVec.ofNat 64 o, 4⟩] s.mem t.mem := by
    rw [u.mem, scr_addr hp (by omega_arith)]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine k t (h.step (by rw [u.gpr]) (by rw [u.gpr]) u.rd u.wr ?_) u.mem u.gpr
    (fun d hd => lw_keep hp f (fun r hr => ?_) hd) f
  · rw [u.mem]; exact (Frame.refl _ _).writeW (r := scrR s₀) (by simp) _ hc
  · simp only [List.mem_singleton] at hr; subst hr
    exact ⟨scrR s₀, by simp, scr_sub (by omega_arith)⟩

omit hp in
/-- A store to `scratch` from offset 192 on keeps the streaming state. -/
theorem repr_store {m m' : Mem} {o : Nat} (ho : 192 ≤ o) (ho' : o + 4 ≤ 16384)
    (f : Frame [⟨(scrP s₀).setWidth 64 + BitVec.ofNat 64 o, 4⟩] m m') {data : List Byte}
    (h : Repr b (Spec.Blake2.init b 64 0) m ((scrP s₀).setWidth 64) data) :
    Repr b (Spec.Blake2.init b 64 0) m' ((scrP s₀).setWidth 64) data :=
  HPrime.repr_frame f (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.base_disjoint _ ho (by omega_arith)) h

end

/-- The bytes at `p`: a word, then the rest. -/
theorem bytes_word (m : Mem) (p : Addr) (n : Nat) :
    bytesAt m p (4 + n) = Spec.Blake2.wordBytes (m.readW p 32) ++ bytesAt m (p + BitVec.ofNat 64 4) n := by
  rw [Proof.Blake2.bytesAt_add, Proof.Blake2.wordBytes_readW (w := 32) m p (.inl rfl)]

theorem variant_code {s₀ : State} (hk : (kindV s₀).toNat ≤ 2) : (prm s₀).variant.code = (kindV s₀).toNat := by
  simp only [prm]
  rcases (by omega_arith : (kindV s₀).toNat = 0 ∨ (kindV s₀).toNat = 1 ∨ (kindV s₀).toNat = 2) with h | h | h <;>
    simp [h, Spec.Argon2.Variant.code, Spec.Argon2.params]

theorem le32_arg (x : BitVec 32) : Spec.Argon2.le32 x.toNat = Spec.Blake2.wordBytes x := by
  simp only [Spec.Argon2.le32, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem header_eq : Impl.Argon2.X86.Derive.header =
    [.mov .eax (.mem ⟨.ebp, argOff 7⟩), .store ⟨.ebx, 768⟩ .eax,
     .mov .eax (.mem ⟨.ebp, argOff 17⟩), .store ⟨.ebx, 772⟩ .eax,
     .mov .eax (.mem ⟨.ebp, argOff 6⟩), .store ⟨.ebx, 776⟩ .eax,
     .mov .eax (.mem ⟨.ebp, argOff 5⟩), .store ⟨.ebx, 780⟩ .eax,
     .mov .eax (.imm 0x13), .store ⟨.ebx, 784⟩ .eax,
     .mov .eax (.mem ⟨.ebp, argOff 0⟩), .store ⟨.ebx, 788⟩ .eax] := rfl

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- A word of `scratch` is kept by a store to another one. -/
theorem scr_keep {m m' : Mem} {o o' : Nat} (ho : o + 4 ≤ 16384) (ho' : o' + 4 ≤ 16384)
    (hd : o + 4 ≤ o' ∨ o' + 4 ≤ o)
    (f : Frame [⟨(scrP s₀).setWidth 64 + BitVec.ofNat 64 o', 4⟩] m m') :
    m'.readW (addr (scrP s₀) o) 32 = m.readW (addr (scrP s₀) o) 32 := by
  rw [scr_addr hp (by omega_arith)]
  refine f.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_singleton] at hr; subst hr
  exact Offset.disjoint _ hd (by omega_arith) (by omega_arith)

/-- The six header words, at `scratch + 768`. -/
theorem header_ok {s : State} (h : Inv s₀ s) (pr : Prm s₀ s) (hb : s.gpr .ebx = scrP s₀)
    (repr : Repr b (Spec.Blake2.init b 64 0) s.mem ((scrP s₀).setWidth 64) []) :
    WP isa (.block Impl.Argon2.X86.Derive.header) s fun t => Inv s₀ t ∧ Prm s₀ t ∧
      t.gpr .ebx = scrP s₀ ∧ Repr b (Spec.Blake2.init b 64 0) t.mem ((scrP s₀).setWidth 64) [] ∧
      bytesAt t.mem ((scrP s₀).setWidth 64 + BitVec.ofNat 64 768) 24 = Proof.Argon2.initialHeader (prm s₀) ∧
      ∀ d, d + 4 ≤ 144 → lw s₀ t d = lw s₀ s d := by
  rw [header_eq]
  refine wp_ldarg hp h (i := 7) (by decide) fun s₁ u₁ => ?_
  obtain i₁ := h.upd u₁ (by decide) (by decide)
  obtain b₁ : s₁.gpr .ebx = scrP s₀ := by rw [u₁.other _ (by decide), hb]
  refine wp_stscr hp i₁ b₁ (o := 768) (by decide) fun s₂ i₂ m₂ g₂ l₂ f₂ => ?_
  obtain b₂ : s₂.gpr .ebx = scrP s₀ := by rw [g₂, b₁]
  refine wp_ldarg hp i₂ (i := 17) (by decide) fun s₃ u₃ => ?_
  obtain i₃ := i₂.upd u₃ (by decide) (by decide)
  obtain b₃ : s₃.gpr .ebx = scrP s₀ := by rw [u₃.other _ (by decide), b₂]
  refine wp_stscr hp i₃ b₃ (o := 772) (by decide) fun s₄ i₄ m₄ g₄ l₄ f₄ => ?_
  obtain b₄ : s₄.gpr .ebx = scrP s₀ := by rw [g₄, b₃]
  refine wp_ldarg hp i₄ (i := 6) (by decide) fun s₅ u₅ => ?_
  obtain i₅ := i₄.upd u₅ (by decide) (by decide)
  obtain b₅ : s₅.gpr .ebx = scrP s₀ := by rw [u₅.other _ (by decide), b₄]
  refine wp_stscr hp i₅ b₅ (o := 776) (by decide) fun s₆ i₆ m₆ g₆ l₆ f₆ => ?_
  obtain b₆ : s₆.gpr .ebx = scrP s₀ := by rw [g₆, b₅]
  refine wp_ldarg hp i₆ (i := 5) (by decide) fun s₇ u₇ => ?_
  obtain i₇ := i₆.upd u₇ (by decide) (by decide)
  obtain b₇ : s₇.gpr .ebx = scrP s₀ := by rw [u₇.other _ (by decide), b₆]
  refine wp_stscr hp i₇ b₇ (o := 780) (by decide) fun s₈ i₈ m₈ g₈ l₈ f₈ => ?_
  obtain b₈ : s₈.gpr .ebx = scrP s₀ := by rw [g₈, b₇]
  refine wp_movi fun s₉ u₉ => ?_
  obtain i₉ := i₈.upd u₉ (by decide) (by decide)
  obtain b₉ : s₉.gpr .ebx = scrP s₀ := by rw [u₉.other _ (by decide), b₈]
  refine wp_stscr hp i₉ b₉ (o := 784) (by decide) fun s₁₀ i₁₀ m₁₀ g₁₀ l₁₀ f₁₀ => ?_
  obtain b₁₀ : s₁₀.gpr .ebx = scrP s₀ := by rw [g₁₀, b₉]
  refine wp_ldarg hp i₁₀ (i := 0) (by decide) fun s₁₁ u₁₁ => ?_
  obtain i₁₁ := i₁₀.upd u₁₁ (by decide) (by decide)
  obtain b₁₁ : s₁₁.gpr .ebx = scrP s₀ := by rw [u₁₁.other _ (by decide), b₁₀]
  refine wp_stscr hp i₁₁ b₁₁ (o := 788) (by decide) fun t it mt gt lt ft => WP.block_nil ?_
  -- The locals.
  obtain L : ∀ d, d + 4 ≤ 144 → lw s₀ t d = lw s₀ s d := fun d hd => by
    rw [lt d hd, lw_mem u₁₁.mem, l₁₀ d hd, lw_mem u₉.mem, l₈ d hd, lw_mem u₇.mem, l₆ d hd, lw_mem u₅.mem,
      l₄ d hd, lw_mem u₃.mem, l₂ d hd, lw_mem u₁.mem]
  -- The streaming state.
  obtain R : Repr b (Spec.Blake2.init b 64 0) t.mem ((scrP s₀).setWidth 64) [] := by
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
  obtain w0 : t.mem.readW (addr (scrP s₀) 768) 32 = arg s₀ 7 := by
    rw [scr_keep hp (by decide) (by decide) (by decide) ft, u₁₁.mem,
      scr_keep hp (by decide) (by decide) (by decide) f₁₀, u₉.mem,
      scr_keep hp (by decide) (by decide) (by decide) f₈, u₇.mem,
      scr_keep hp (by decide) (by decide) (by decide) f₆, u₅.mem,
      scr_keep hp (by decide) (by decide) (by decide) f₄, u₃.mem, m₂, Mem.readW_writeW_self32, u₁.gpr]
  obtain w1 : t.mem.readW (addr (scrP s₀) 772) 32 = arg s₀ 17 := by
    rw [scr_keep hp (by decide) (by decide) (by decide) ft, u₁₁.mem,
      scr_keep hp (by decide) (by decide) (by decide) f₁₀, u₉.mem,
      scr_keep hp (by decide) (by decide) (by decide) f₈, u₇.mem,
      scr_keep hp (by decide) (by decide) (by decide) f₆, u₅.mem, m₄, Mem.readW_writeW_self32, u₃.gpr]
  obtain w2 : t.mem.readW (addr (scrP s₀) 776) 32 = arg s₀ 6 := by
    rw [scr_keep hp (by decide) (by decide) (by decide) ft, u₁₁.mem,
      scr_keep hp (by decide) (by decide) (by decide) f₁₀, u₉.mem,
      scr_keep hp (by decide) (by decide) (by decide) f₈, u₇.mem, m₆, Mem.readW_writeW_self32, u₅.gpr]
  obtain w3 : t.mem.readW (addr (scrP s₀) 780) 32 = arg s₀ 5 := by
    rw [scr_keep hp (by decide) (by decide) (by decide) ft, u₁₁.mem,
      scr_keep hp (by decide) (by decide) (by decide) f₁₀, u₉.mem, m₈, Mem.readW_writeW_self32, u₇.gpr]
  obtain w4 : t.mem.readW (addr (scrP s₀) 784) 32 = 0x13 := by
    rw [scr_keep hp (by decide) (by decide) (by decide) ft, u₁₁.mem, m₁₀, Mem.readW_writeW_self32, u₉.gpr]
  obtain w5 : t.mem.readW (addr (scrP s₀) 788) 32 = arg s₀ 0 := by
    rw [mt, Mem.readW_writeW_self32, u₁₁.gpr]
  obtain a : ∀ o, o < 16384 → (scrP s₀).setWidth 64 + BitVec.ofNat 64 o = addr (scrP s₀) o :=
    fun o ho => (scr_addr hp ho).symm
  obtain step : ∀ o, (scrP s₀).setWidth 64 + BitVec.ofNat 64 o + BitVec.ofNat 64 4 =
      (scrP s₀).setWidth 64 + BitVec.ofNat 64 (o + 4) := fun o => by
    rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  rw [show (24 : Nat) = 4 + 20 from rfl, bytes_word, step, show (20 : Nat) = 4 + 16 from rfl, bytes_word, step,
    show (16 : Nat) = 4 + 12 from rfl, bytes_word, step, show (12 : Nat) = 4 + 8 from rfl, bytes_word, step,
    show (8 : Nat) = 4 + 4 from rfl, bytes_word, step, show (4 : Nat) = 4 + 0 from rfl, bytes_word]
  simp only [Nat.reduceAdd]
  rw [a 768 (by decide), a 772 (by decide), a 776 (by decide), a 780 (by decide), a 784 (by decide),
    a 788 (by decide), w0, w1, w2, w3, w4, w5]
  simp only [Proof.Argon2.initialHeader, prm, ← le32_arg, List.append_assoc,
    bytesAt, List.range_zero, List.map_nil, List.append_nil]
  obtain vc := variant_code hp.kind_le
  simp only [prm] at vc
  rw [vc]
  rfl

end

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- `n` bytes of `scratch` at offset `d` are writable. -/
theorem scr_cov {s : State} (h : Inv s₀ s) {d n : Nat} (hd : d + n ≤ 16384) :
    Covers [⟨(scrP s₀).setWidth 64 + BitVec.ofNat 64 d, n⟩] s.wr := by
  rw [h.wr]
  exact Covers.of_sub (rs' := [scrR s₀]) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scrR s₀, List.mem_singleton_self _, d, rfl, hd⟩) |>.trans
    fun a n ⟨r, hr, hc⟩ => ⟨r, by simp only [List.mem_singleton] at hr; subst hr; exact scr_mem hp, hc⟩

/-- The stack below the locals is outside `scratch`. -/
theorem stk_scr {d n k : Nat} (hd : d + n ≤ 16384) (hk : k ≤ 84) :
    (VG.X86.below (E s₀) k).Disjoint ⟨(scrP s₀).setWidth 64 + BitVec.ofNat 64 d, n⟩ :=
  ((hp.stk_all (scrR s₀) (by simp)).sub_left fun a ha =>
    call_stk hp a (VG.X86.below_sub hk (by rw [E_nat hp]; have := hp.esp_lo; omega_arith) a ha)).sub_right
    (scr_sub hd)

/-- A store to the locals keeps the streaming state at `scratch`. -/
theorem repr_loc {m : Mem} {d : Nat} (hd : d + 4 ≤ 144) (v : BitVec 32) {h0 : Spec.Blake2.HashValue 64}
    {data : List Byte} (h : Repr b h0 m ((scrP s₀).setWidth 64) data) :
    Repr b h0 (m.writeW (addr (E s₀) d) v) ((scrP s₀).setWidth 64) data :=
  HPrime.repr_frame ((Frame.refl [⟨addr (E s₀) d, 4⟩] m).writeW (List.mem_singleton_self _) v
    (Region.contains_self _ _)) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ((loc_disj hp hd (scrR s₀) (by simp)).symm).sub_left (scr_sub (d := 0) (n := 192) (by decide) |>
        fun hs => by simpa using hs)) h

/-- `start`'s first block: `ebx :=` `scratch`, and the digest length. -/
theorem stA_ok {s : State} (h : Inv s₀ s) (pr : Prm s₀ s) :
    WP isa (.block [.mov .ebx (Impl.Argon2.X86.Derive.fr (argOff 15)), .mov .edx (.imm 64)]) s fun t =>
      Inv s₀ t ∧ Prm s₀ t ∧ t.gpr .ebx = scrP s₀ ∧ t.gpr .edx = BitVec.ofNat 32 64 := by
  refine wp_ldarg hp h (i := 15) (by decide) fun s₁ u₁ => wp_movi fun s₂ u₂ => WP.block_nil ?_
  obtain e : ∀ d, lw s₀ s₂ d = lw s₀ s d := fun d => by rw [lw_mem u₂.mem, lw_mem u₁.mem]
  exact ⟨(h.upd u₁ (by decide) (by decide)).upd u₂ (by decide) (by decide),
    ⟨by rw [e]; exact pr.divisor, by rw [e]; exact pr.segLen, by rw [e]; exact pr.laneLen, by rw [e]; exact pr.stride⟩,
    by rw [u₂.other _ (by decide), u₁.gpr], by rw [u₂.gpr]; rfl⟩

/-- `start`'s `init`. -/
theorem stInit_ok {s : State}
    (h : Inv s₀ s ∧ Prm s₀ s ∧ s.gpr .ebx = scrP s₀ ∧ s.gpr .edx = BitVec.ofNat 32 64) :
    WP isa Impl.Argon2.X86.HPrime.init s fun t => Inv s₀ t ∧ Prm s₀ t ∧ t.gpr .ebx = scrP s₀ ∧
      Repr b (Spec.Blake2.init b 64 0) t.mem ((scrP s₀).setWidth 64) [] :=
  (init_k (ctx hp h.1 h.2.2.1) (n := 64) h.2.2.2 (by decide) (by decide)).mono fun _ ⟨r, k⟩ =>
    let ⟨i, l⟩ := h.1.keeps hp k
    ⟨i, Prm.of_lw h.2.1 fun d hd => l d (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd; rcases hd with rfl | rfl | rfl | rfl <;> decide),
      k.ebx.trans h.2.2.1, r⟩

/-- `start`'s hash of the header. -/
theorem stFix_ok {s : State}
    (h : Inv s₀ s ∧ Prm s₀ s ∧ s.gpr .ebx = scrP s₀ ∧
      Repr b (Spec.Blake2.init b 64 0) s.mem ((scrP s₀).setWidth 64) [] ∧
      bytesAt s.mem ((scrP s₀).setWidth 64 + BitVec.ofNat 64 768) 24 = Proof.Argon2.initialHeader (prm s₀)) :
    WP isa (Impl.Argon2.X86.HPrime.absorbFixed 768 24) s fun t => Inv s₀ t ∧ Prm s₀ t ∧
      t.gpr .ebx = scrP s₀ ∧
      Repr b (Spec.Blake2.init b 64 0) t.mem ((scrP s₀).setWidth 64) (Proof.Argon2.initialHeader (prm s₀)) := by
  have hs := hp.scr_fits
  obtain ⟨i₄, pr₄, b₄, r₄, hd₄⟩ := h
  refine (HPrime.absorbFixed_ok (ctx hp i₄ b₄) (offset := 768) (size := 24) (by omega_arith) (by decide)
    (by decide) (scr_cov hp i₄ (by decide)) (stk_scr hp (by decide) (by decide)) r₄).mono fun s₅ ⟨r₅, k₅⟩ => ?_
  rw [hd₄] at r₅
  obtain ⟨i₅, l₅⟩ := i₄.keeps hp k₅
  exact ⟨i₅, Prm.of_lw pr₄ fun d hd => l₅ d (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd; rcases hd with rfl | rfl | rfl | rfl <;> decide),
    k₅.ebx.trans b₄, r₅⟩

/-- `start`'s count of the header's bytes. -/
theorem stCnt_ok {s : State}
    (h : Inv s₀ s ∧ Prm s₀ s ∧ s.gpr .ebx = scrP s₀ ∧
      Repr b (Spec.Blake2.init b 64 0) s.mem ((scrP s₀).setWidth 64) (Proof.Argon2.initialHeader (prm s₀))) :
    WP isa (.block [.mov .eax (.imm 24), .store ⟨.ebp, countLoOff⟩ .eax, .mov .eax (.imm 0),
      .store ⟨.ebp, countHiOff⟩ .eax]) s (HI s₀ (Proof.Argon2.initialHeader (prm s₀))) := by
  obtain ⟨i₅, pr₄, b₅, r₅⟩ := h
  refine wp_movi fun s₆ u₆ => ?_
  obtain i₆ := i₅.upd u₆ (by decide) (by decide)
  refine wp_stloc hp i₆ (d := countLoOff) (by decide) fun s₇ i₇ v₇ o₇ g₇ m₇ => ?_
  refine wp_movi fun s₈ u₈ => ?_
  obtain i₈ := i₇.upd u₈ (by decide) (by decide)
  refine wp_stloc hp i₈ (d := countHiOff) (by decide) fun t it vt ot gt mt => WP.block_nil ?_
  obtain L : ∀ d, d + 4 ≤ 144 → (d + 4 ≤ countLoOff ∨ countHiOff + 4 ≤ d) → lw s₀ t d = lw s₀ s d :=
    fun d hd hd' => by
      rw [ot d (by omega_arith) (by simp only [countHiOff, countLoOff] at hd' ⊢; omega_arith), lw_mem u₈.mem,
        o₇ d (by omega_arith) (by simp only [countHiOff, countLoOff] at hd' ⊢; omega_arith), lw_mem u₆.mem]
  refine ⟨it, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [L _ (by decide) (by decide)]; exact pr₄.divisor
  · rw [L _ (by decide) (by decide)]; exact pr₄.segLen
  · rw [L _ (by decide) (by decide)]; exact pr₄.laneLen
  · rw [L _ (by decide) (by decide)]; exact pr₄.stride
  · rw [gt, u₈.other _ (by decide), g₇, u₆.other _ (by decide), b₅]
  · rw [mt, u₈.mem, m₇, u₆.mem]
    exact repr_loc hp (by decide) _ (repr_loc hp (by decide) _ r₅)
  · rw [ot _ (by decide) (by decide), lw_mem u₈.mem, v₇, u₆.gpr, Proof.Argon2.initialHeader_length]; rfl
  · rw [vt, u₈.gpr, Proof.Argon2.initialHeader_length]; rfl
  · rw [Proof.Argon2.initialHeader_length]; decide

theorem start_ok {s : State} (h : Inv s₀ s) (pr : Prm s₀ s) :
    WP isa Impl.Argon2.X86.Derive.start s (HI s₀ (Proof.Argon2.initialHeader (prm s₀))) := by
  unfold Impl.Argon2.X86.Derive.start
  refine WP.seq ((stA_ok hp h pr).mono fun s₂ h₂ => WP.seq ((stInit_ok hp h₂).mono fun s₃ ⟨i₃, pr₃, b₃, r₃⟩ =>
    WP.seq ((header_ok hp i₃ pr₃ b₃ r₃).mono fun s₄ ⟨i₄, pr₄, b₄, r₄, hd₄, _⟩ =>
      WP.seq ((stFix_ok hp ⟨i₄, pr₄, b₄, r₄, hd₄⟩).mono fun s₅ h₅ => stCnt_ok hp h₅))))

end

/-- `add d, src`, for a source of known value, and the carry. -/
theorem wp_addC {s : State} {d : Reg} {src : Src} {v : BitVec 32} (hv : readSrc s src = some v)
    {is : List Instr} {Q : State → Prop}
    (k : ∀ s', Upd s s' d (s.gpr d + v) → s'.cf = some (decide (2 ^ 32 ≤ (s.gpr d).toNat + v.toNat)) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.alu .add d src :: is)) s Q :=
  VG.X86.Wp.cons (by simp [exec, execAlu, hv]; rfl) (k _ (Upd.flags _ _ _ _ _ _) rfl)

/-- `adc d, 0`, with a known carry. -/
theorem wp_adc0 {s : State} {d : Reg} {c : Bool} (hc : s.cf = some c) {is : List Instr} {Q : State → Prop}
    (k : ∀ s', Upd s s' d (s.gpr d + 0 + (BitVec.ofBool c).setWidth 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .adc d (.imm 0) :: is)) s Q :=
  VG.X86.Wp.cons (by simp [exec, execAlu, readSrc, hc]; rfl) (k _ (Upd.flags _ _ _ _ _ _))

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- `addCount`: the 64-bit count in the locals, `c`, plus `x`. -/
theorem count_ok {s : State} (h : Inv s₀ s) {c x : Nat} (hx : x < 2 ^ 32)
    (lo : lw s₀ s countLoOff = BitVec.ofNat 32 c) (hi : lw s₀ s countHiOff = BitVec.ofNat 32 (c / 2 ^ 32))
    {src : Src} (hsrc : ∀ t, Inv s₀ t → t.mem = s.mem → readSrc t src = some (BitVec.ofNat 32 x))
    {is : List Instr} {Q : State → Prop}
    (k : ∀ t, Inv s₀ t → lw s₀ t countLoOff = BitVec.ofNat 32 (c + x) →
      lw s₀ t countHiOff = BitVec.ofNat 32 ((c + x) / 2 ^ 32) →
      (∀ e, e + 4 ≤ 236 → (e + 4 ≤ countLoOff ∨ countHiOff + 4 ≤ e) → lw s₀ t e = lw s₀ s e) →
      (∀ r, r ≠ .ecx → r ≠ .edx → t.gpr r = s.gpr r) →
      t.mem = (s.mem.writeW (addr (E s₀) countLoOff) (BitVec.ofNat 32 (c + x))).writeW
        (addr (E s₀) countHiOff) (BitVec.ofNat 32 ((c + x) / 2 ^ 32)) →
      t.gpr .ecx = BitVec.ofNat 32 (c + x) → t.gpr .edx = BitVec.ofNat 32 ((c + x) / 2 ^ 32) →
      WP isa (.block is) t Q) :
    WP isa (.block (Impl.Argon2.X86.Derive.addCount src ++ is)) s Q := by
  simp only [Impl.Argon2.X86.Derive.addCount, Impl.Argon2.X86.Derive.fr, List.cons_append, List.nil_append]
  refine wp_ldloc hp h (d := countLoOff) (by decide) fun s₁ u₁ => ?_
  obtain i₁ := h.upd u₁ (by decide) (by decide)
  refine wp_ldloc hp i₁ (d := countHiOff) (by decide) fun s₂ u₂ => ?_
  obtain i₂ := i₁.upd u₂ (by decide) (by decide)
  obtain m₂ : s₂.mem = s.mem := by rw [u₂.mem, u₁.mem]
  refine wp_addC (hsrc s₂ i₂ m₂) fun s₃ u₃ c₃ => ?_
  obtain i₃ := i₂.upd u₃ (by decide) (by decide)
  refine wp_adc0 c₃ fun s₄ u₄ => ?_
  obtain i₄ := i₃.upd u₄ (by decide) (by decide)
  obtain e₁ : s₂.gpr .ecx = BitVec.ofNat 32 c := by rw [u₂.other _ (by decide), u₁.gpr, lo]
  obtain vlo : s₄.gpr .ecx = BitVec.ofNat 32 (c + x) := by
    rw [u₄.other _ (by decide), u₃.gpr, e₁, BitVec.ofNat_add]
  obtain vhi : s₄.gpr .edx = BitVec.ofNat 32 ((c + x) / 2 ^ 32) := by
    obtain z : ∀ y : BitVec 32, y + 0 = y := fun y => by simp
    rw [u₄.gpr, u₃.other _ (by decide), u₂.gpr, lw_mem u₁.mem, hi, e₁, z]
    exact Proof.Blake2.X86.Stream.carry_ofNat c x hx
  refine wp_stloc hp i₄ (d := countLoOff) (by decide) fun s₅ i₅ v₅ o₅ g₅ m₅ => ?_
  refine wp_stloc hp i₅ (d := countHiOff) (by decide) fun t it vt ot gt mt => k t it ?_ ?_ ?_ ?_ ?_
    (by rw [gt, g₅, vlo]) (by rw [gt, g₅, vhi])
  · rw [ot _ (by decide) (by decide), v₅, vlo]
  · rw [vt, g₅, vhi]
  · intro e he hd
    rw [ot e he (by simp only [countHiOff, countLoOff] at hd ⊢; omega_arith),
      o₅ e he (by simp only [countHiOff, countLoOff] at hd ⊢; omega_arith), lw_mem u₄.mem, lw_mem u₃.mem,
      lw_mem m₂]
  · intro r h1 h2
    rw [gt, g₅, u₄.other _ h2, u₃.other _ h1, u₂.other _ h2, u₁.other _ h1]
  · rw [mt, m₅, g₅, vhi, vlo, u₄.mem, u₃.mem, m₂]

end

theorem count64 {n : Nat} (h : n < 2 ^ 64) :
    BitVec.ofNat 32 (n / 2 ^ 32) ++ BitVec.ofNat 32 n = BitVec.ofNat 64 n :=
  BitVec.eq_of_toNat_eq (by rw [Proof.Blake2.X86.Stream.append_ofNat h, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt h])

/-- H₀'s streaming state at `scratch`, with `data` absorbed and the count `c` in
the locals. -/
structure HC (s₀ : State) (data : List Byte) (c : Nat) (s : State) : Prop where
  inv : Inv s₀ s
  prm : Prm s₀ s
  ebx : s.gpr .ebx = scrP s₀
  repr : Repr b (Spec.Blake2.init b 64 0) s.mem ((scrP s₀).setWidth 64) data
  lo : lw s₀ s countLoOff = BitVec.ofNat 32 c
  hi : lw s₀ s countHiOff = BitVec.ofNat 32 (c / 2 ^ 32)

theorem HI.hc {s₀ s : State} {data : List Byte} (h : HI s₀ data s) : HC s₀ data data.length s :=
  ⟨h.inv, h.prm, h.ebx, h.repr, h.lo, h.hi⟩

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- `absorb`'s first block: LE32 of the length at `scratch + 792`, and `update`'s arguments. -/
theorem absA_ok {len : Nat} (hlen : len < 18) {data : List Byte} {c : Nat} {s : State} (h : HC s₀ data c s) :
    WP isa (.block [.mov .eax (Impl.Argon2.X86.Derive.fr (argOff len)), .store ⟨.ebx, 792⟩ .eax,
      .mov .ecx (Impl.Argon2.X86.Derive.fr countLoOff), .mov .edx (Impl.Argon2.X86.Derive.fr countHiOff),
      .mov .esi (.reg .ebx), .alu .add .esi (.imm 792), .mov .edi (.imm 4)]) s fun t =>
      HC s₀ data c t ∧ t.gpr .esi = scrP s₀ + 792 ∧ (t.gpr .edi).toNat = 4 ∧ t.gpr .ecx = BitVec.ofNat 32 c ∧
      t.gpr .edx = BitVec.ofNat 32 (c / 2 ^ 32) ∧
      bytesAt t.mem ((scrP s₀ + 792).setWidth 64) 4 = Spec.Argon2.le32 (arg s₀ len).toNat := by
  have hs := hp.scr_fits
  simp only [Impl.Argon2.X86.Derive.fr]
  refine wp_ldarg hp h.inv (i := len) hlen fun s₁ u₁ => ?_
  obtain i₁ := h.inv.upd u₁ (by decide) (by decide)
  obtain b₁ : s₁.gpr .ebx = scrP s₀ := by rw [u₁.other _ (by decide), h.ebx]
  refine wp_stscr hp i₁ b₁ (o := 792) (by decide) fun s₂ i₂ m₂ g₂ l₂ f₂ => ?_
  refine wp_ldloc hp i₂ (d := countLoOff) (by decide) fun s₃ u₃ => ?_
  refine wp_ldloc hp (i₂.upd u₃ (by decide) (by decide)) (d := countHiOff) (by decide) fun s₄ u₄ => ?_
  refine wp_mov fun s₅ u₅ => wp_addi fun s₆ u₆ => wp_movi fun s₇ u₇ => WP.block_nil ?_
  obtain i₇ := ((((i₂.upd u₃ (by decide) (by decide)).upd u₄ (by decide) (by decide)).upd u₅ (by decide)
    (by decide)).upd u₆ (by decide) (by decide)).upd u₇ (by decide) (by decide)
  obtain m₇ : s₇.mem = s₂.mem := by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem]
  obtain L₂ : ∀ d, d + 4 ≤ 144 → lw s₀ s₂ d = lw s₀ s d := fun d hd => by rw [l₂ d hd, lw_mem u₁.mem]
  obtain L₇ : ∀ d, d + 4 ≤ 144 → lw s₀ s₇ d = lw s₀ s d := fun d hd => by rw [lw_mem m₇, L₂ d hd]
  obtain e792 : (scrP s₀ + 792).setWidth 64 = (scrP s₀).setWidth 64 + BitVec.ofNat 64 792 :=
    HPrime.setWidth_add (d := 792) (by omega_arith)
  refine ⟨⟨i₇, Prm.of_lw h.prm fun d hd => L₇ d (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd; rcases hd with rfl | rfl | rfl | rfl <;> decide),
    by rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), g₂, b₁],
    by rw [m₇]; exact repr_store (by decide) (by decide) f₂ (by rw [u₁.mem]; exact h.repr),
    by rw [L₇ _ (by decide)]; exact h.lo, by rw [L₇ _ (by decide)]; exact h.hi⟩, ?_, by rw [u₇.gpr]; rfl, ?_, ?_, ?_⟩
  · rw [u₇.other _ (by decide), u₆.gpr, u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), g₂, b₁]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.gpr, L₂ _ (by decide), h.lo]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, lw_mem u₃.mem,
      L₂ _ (by decide), h.hi]
  · rw [e792, show (4 : Nat) = 4 + 0 from rfl, bytes_word, ← scr_addr hp (by decide), m₇, m₂,
      Mem.readW_writeW_self32, u₁.gpr, le32_arg]
    rfl

/-- `absorb`'s first `update`: LE32 of the length. -/
theorem absU1_ok {len : Nat} {data : List Byte} {c : Nat} {s : State} (h : HC s₀ data c s)
    (hd : data.length = c) (hc : c + 4 < 2 ^ 36) (esi : s.gpr .esi = scrP s₀ + 792) (edi : (s.gpr .edi).toNat = 4)
    (ecx : s.gpr .ecx = BitVec.ofNat 32 c) (edx : s.gpr .edx = BitVec.ofNat 32 (c / 2 ^ 32))
    (w : bytesAt s.mem ((scrP s₀ + 792).setWidth 64) 4 = Spec.Argon2.le32 (arg s₀ len).toNat) :
    WP isa Impl.Argon2.X86.HPrime.update s (HC s₀ (data ++ Spec.Argon2.le32 (arg s₀ len).toNat) c) := by
  have hs := hp.scr_fits
  obtain e792 : (scrP s₀ + 792).setWidth 64 = (scrP s₀).setWidth 64 + BitVec.ofNat 64 792 :=
    HPrime.setWidth_add (d := 792) (by omega_arith)
  refine (update_k (ctx hp h.inv h.ebx) (D := scrP s₀ + 792) (L := 4) esi edi
    (by have : (scrP s₀ + 792).toNat = (scrP s₀).toNat + 792 := add_nat (k := 792) (by omega_arith)
        omega_arith)
    (by rw [e792]; exact Covers.right (scr_cov hp h.inv (by decide)))
    (by rw [e792]; exact Offset.disjoint_base _ (by decide) (by decide))
    (by rw [e792]; exact stk_scr hp (by decide) (by decide)) h.repr
    (by rw [edx, ecx, hd]; exact count64 (by omega_arith)) (by omega_arith)).mono fun t ⟨r, k⟩ => ?_
  obtain ⟨i, l⟩ := h.inv.keeps hp k
  rw [w] at r
  exact ⟨i, Prm.of_lw h.prm fun d hd => l d (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd; rcases hd with rfl | rfl | rfl | rfl <;> decide),
    k.ebx.trans h.ebx, r, by rw [l _ (by decide)]; exact h.lo, by rw [l _ (by decide)]; exact h.hi⟩

/-- `absorb`'s second block: the count advanced by 4, and `update`'s arguments. -/
theorem absB_ok {ptr len : Nat} (hptr : ptr < 18) (hlen : len < 18) {data : List Byte} {c : Nat} {s : State}
    (h : HC s₀ data c s) :
    WP isa (.block (Impl.Argon2.X86.Derive.addCount (.imm 4) ++
      ([.mov .esi (Impl.Argon2.X86.Derive.fr (argOff ptr)), .mov .edi (Impl.Argon2.X86.Derive.fr (argOff len))] :
        List Instr)))
      s fun t => HC s₀ data (c + 4) t ∧ t.gpr .esi = arg s₀ ptr ∧ (t.gpr .edi).toNat = (arg s₀ len).toNat ∧
        t.gpr .ecx = BitVec.ofNat 32 (c + 4) ∧ t.gpr .edx = BitVec.ofNat 32 ((c + 4) / 2 ^ 32) := by
  refine count_ok hp h.inv (x := 4) (by decide) h.lo h.hi (fun _ _ _ => rfl)
    fun s₉ i₉ lo₉ hi₉ o₉ g₉ m₉ c₉ d₉ => wp_ldarg hp i₉ (i := ptr) hptr fun s₁₀ u₁₀ =>
      wp_ldarg hp (i₉.upd u₁₀ (by decide) (by decide)) (i := len) hlen fun s₁₁ u₁₁ => WP.block_nil ?_
  obtain i₁₁ := (i₉.upd u₁₀ (by decide) (by decide)).upd u₁₁ (by decide) (by decide)
  obtain m₁₁ : s₁₁.mem = s₉.mem := by rw [u₁₁.mem, u₁₀.mem]
  refine ⟨⟨i₁₁, Prm.of_lw h.prm fun d hd => ?_, ?_, ?_, by rw [lw_mem m₁₁]; exact lo₉, by rw [lw_mem m₁₁]; exact hi₉⟩,
    by rw [u₁₁.other _ (by decide), u₁₀.gpr], by rw [u₁₁.gpr],
    by rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), c₉],
    by rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), d₉]⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    obtain hd' : d + 4 ≤ 144 ∧ (d + 4 ≤ countLoOff ∨ countHiOff + 4 ≤ d) := by
      rcases hd with rfl | rfl | rfl | rfl <;> decide
    rw [lw_mem m₁₁, o₉ d (by omega_arith) hd'.2]
  · rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), g₉ _ (by decide) (by decide), h.ebx]
  · rw [m₁₁, m₉]; exact repr_loc hp (by decide) _ (repr_loc hp (by decide) _ h.repr)

/-- `absorb`'s second `update`: the input. -/
theorem absU2_ok {ptr len : Nat}
    (hR : (⟨(arg s₀ ptr).setWidth 64, (arg s₀ len).toNat⟩ : Region) ∈ [pwR s₀, saltR s₀, secR s₀, adR s₀])
    (hfit : (arg s₀ ptr).toNat + (arg s₀ len).toNat ≤ 2 ^ 32) {data : List Byte} {c : Nat} {s : State}
    (h : HC s₀ data c s) (hd : data.length = c) (hc : c + 2 ^ 32 < 2 ^ 36) (esi : s.gpr .esi = arg s₀ ptr)
    (edi : (s.gpr .edi).toNat = (arg s₀ len).toNat) (ecx : s.gpr .ecx = BitVec.ofNat 32 c)
    (edx : s.gpr .edx = BitVec.ofNat 32 (c / 2 ^ 32)) :
    WP isa Impl.Argon2.X86.HPrime.update s
      (HC s₀ (data ++ bytesAt s₀.mem ((arg s₀ ptr).setWidth 64) (arg s₀ len).toNat) c) := by
  obtain hlt := (arg s₀ len).isLt
  obtain hR' : (⟨(arg s₀ ptr).setWidth 64, (arg s₀ len).toNat⟩ : Region) ∈
      [pwR s₀, saltR s₀, secR s₀, adR s₀, argR s₀] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR ⊢
    rcases hR with h | h | h | h <;> simp [h]
  obtain hS : (⟨(arg s₀ ptr).setWidth 64, (arg s₀ len).toNat⟩ : Region) ∈
      [pwR s₀, saltR s₀, secR s₀, adR s₀, memR s₀, scrR s₀, outR s₀] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR ⊢
    rcases hR with h | h | h | h <;> simp [h]
  obtain rin := hp.ro_w _ hR' (scrR s₀) (by simp)
  refine (update_k (ctx hp h.inv h.ebx) (D := arg s₀ ptr) (L := (arg s₀ len).toNat) esi edi hfit
    (by rw [h.inv.rd, hp.rd]
        exact Covers.of_sub fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact ⟨_, List.mem_append_left _ hR', 0, by simp, by simp⟩)
    (rin.sub_right (Region.sub_prefix (by decide)))
    ((hp.stk_all _ hS).sub_left fun a ha => call_stk hp a (below60_call hp a ha))
    h.repr (by rw [edx, ecx, hd]; exact count64 (by omega_arith)) (by omega_arith)).mono fun t ⟨r, k⟩ => ?_
  obtain ⟨i, l⟩ := h.inv.keeps hp k
  obtain inp : bytesAt s.mem ((arg s₀ ptr).setWidth 64) (arg s₀ len).toNat =
      bytesAt s₀.mem ((arg s₀ ptr).setWidth 64) (arg s₀ len).toNat :=
    h.inv.input hp (R := ⟨(arg s₀ ptr).setWidth 64, (arg s₀ len).toNat⟩) hR
  rw [inp] at r
  exact ⟨i, Prm.of_lw h.prm fun d hd => l d (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd; rcases hd with rfl | rfl | rfl | rfl <;> decide),
    k.ebx.trans h.ebx, r, by rw [l _ (by decide)]; exact h.lo, by rw [l _ (by decide)]; exact h.hi⟩

/-- `absorb`'s last block: the count advanced by the input's length. -/
theorem absC_ok {len : Nat} (hlen : len < 18) {data : List Byte} {c : Nat} {s : State} (h : HC s₀ data c s) :
    WP isa (.block (Impl.Argon2.X86.Derive.addCount (Impl.Argon2.X86.Derive.fr (argOff len)))) s
      (HC s₀ data (c + (arg s₀ len).toNat)) := by
  rw [← List.append_nil (Impl.Argon2.X86.Derive.addCount _)]
  refine count_ok hp h.inv (x := (arg s₀ len).toNat) (arg s₀ len).isLt h.lo h.hi
    (fun t it mt => by
      show readSrc t (.mem ⟨.ebp, argOff len⟩) = _
      rw [VG.X86.Wp.readSrc_mem it.ebp (it.arg_in hp hlen), it.arg hp hlen, BitVec.ofNat_toNat,
        BitVec.setWidth_eq])
    fun t it lo hi o g mt _ _ => WP.block_nil ⟨it, Prm.of_lw h.prm fun d hd => ?_, ?_, ?_, lo, hi⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    obtain hd' : d + 4 ≤ 144 ∧ (d + 4 ≤ countLoOff ∨ countHiOff + 4 ≤ d) := by
      rcases hd with rfl | rfl | rfl | rfl <;> decide
    rw [o d (by omega_arith) hd'.2]
  · rw [g _ (by decide) (by decide), h.ebx]
  · rw [mt]; exact repr_loc hp (by decide) _ (repr_loc hp (by decide) _ h.repr)

theorem absorb_ok {ptr len : Nat} (hptr : ptr < 18) (hlen : len < 18)
    (hR : (⟨(arg s₀ ptr).setWidth 64, (arg s₀ len).toNat⟩ : Region) ∈ [pwR s₀, saltR s₀, secR s₀, adR s₀])
    (hfit : (arg s₀ ptr).toNat + (arg s₀ len).toNat ≤ 2 ^ 32) {data : List Byte}
    (hd : data.length + 4 + 2 ^ 32 < 2 ^ 36) {s : State} (h : HI s₀ data s) :
    WP isa (Impl.Argon2.X86.Derive.absorb ptr len) s
      (HI s₀ (Proof.Argon2.appendInput data (bytesAt s₀.mem ((arg s₀ ptr).setWidth 64) (arg s₀ len).toNat))) := by
  obtain hlt := (arg s₀ len).isLt
  unfold Impl.Argon2.X86.Derive.absorb
  refine WP.seq ((absA_ok hp hlen h.hc).mono fun s₁ ⟨h₁, e₁, d₁, c₁, x₁, w₁⟩ => ?_)
  refine WP.seq ((absU1_ok hp h₁ rfl (by omega_arith) e₁ d₁ c₁ x₁ w₁).mono fun s₂ h₂ => ?_)
  refine WP.seq ((absB_ok hp hptr hlen h₂).mono fun s₃ ⟨h₃, e₃, d₃, c₃, x₃⟩ => ?_)
  refine WP.seq ((absU2_ok hp hR hfit h₃ (by simp [Proof.Argon2.le32_length]) (by omega_arith) e₃ d₃ c₃ x₃).mono
    fun s₄ h₄ => ?_)
  refine (absC_ok hp hlen h₄).mono fun t ht => ?_
  obtain hd' : Proof.Argon2.appendInput data (bytesAt s₀.mem ((arg s₀ ptr).setWidth 64) (arg s₀ len).toNat) =
      data ++ Spec.Argon2.le32 (arg s₀ len).toNat ++
        bytesAt s₀.mem ((arg s₀ ptr).setWidth 64) (arg s₀ len).toNat := by
    simp only [Proof.Argon2.appendInput, bytesAt, List.length_map, List.length_range]
  obtain hl : (Proof.Argon2.appendInput data (bytesAt s₀.mem ((arg s₀ ptr).setWidth 64) (arg s₀ len).toNat)).length =
      data.length + 4 + (arg s₀ len).toNat := by
    rw [Proof.Argon2.appendInput_length]; simp only [bytesAt, List.length_map, List.length_range]
  refine ⟨ht.inv, ht.prm, ht.ebx, by rw [hd']; exact ht.repr, by rw [hl]; exact ht.lo, by rw [hl]; exact ht.hi,
    by rw [hl]; omega_arith⟩

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
    (m.writeW (addr (E s₀) d) v).readW (addr (scrP s₀) o) 32 = m.readW (addr (scrP s₀) o) 32 := by
  refine ((Frame.refl [⟨addr (E s₀) d, 4⟩] m).writeW (List.mem_singleton_self _) v
    (Region.contains_self _ _)).readW (r := ⟨addr (scrP s₀) o, 4⟩) (Region.contains_self _ _) ?_ (by decide)
  intro r hr
  simp only [List.mem_singleton] at hr; subst hr
  rw [scr_addr hp (by omega_arith)]
  exact ((loc_disj hp hd (scrR s₀) (by simp)).symm.sub_left (scr_sub ho))

/-- The first `k` words of the digest, copied to the locals. -/
theorem copy_ok {s : State} (h : Inv s₀ s) (hb : s.gpr .ebx = scrP s₀) :
    ∀ k ≤ 16, WP isa (.block ((List.range k).flatMap Impl.Argon2.X86.Derive.copyWord)) s fun t =>
      Inv s₀ t ∧ t.gpr .ebx = scrP s₀ ∧
      (∀ j < k, lw s₀ t (4 * j) = s.mem.readW (addr (scrP s₀) (768 + 4 * j)) 32) ∧
      (∀ o, o + 4 ≤ 16384 → t.mem.readW (addr (scrP s₀) o) 32 = s.mem.readW (addr (scrP s₀) o) 32) ∧
      (∀ e, e + 4 ≤ 236 → 4 * k ≤ e → lw s₀ t e = lw s₀ s e)
  | 0, _ => WP.block_nil ⟨h, hb, fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ => rfl, fun _ _ _ => rfl⟩
  | k + 1, hk => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine WP.block_append ((copy_ok h hb k (by omega_arith)).mono fun t ⟨it, bt, wt, st, lt⟩ => ?_)
    simp only [Impl.Argon2.X86.Derive.copyWord]
    refine VG.X86.Wp.wp_ldm bt (by
        rw [it.rd, it.wr]
        exact ⟨scrR s₀, List.mem_append_right _ (scr_mem hp), by
          rw [scr_addr hp (by omega_arith)]; exact Offset.contains_base _ (by omega_arith) (by omega_arith)⟩)
      fun t₁ u₁ => ?_
    obtain i₁ := it.upd u₁ (by decide) (by decide)
    refine wp_stloc hp i₁ (d := 4 * k) (by omega_arith) fun t₂ i₂ v₂ o₂ g₂ m₂ => WP.block_nil
      ⟨i₂, by rw [g₂, u₁.other _ (by decide), bt], fun j hj => ?_, fun o ho => ?_, fun e he hke => ?_⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · rw [o₂ _ (by omega_arith) (by omega_arith), lw_mem u₁.mem]; exact wt j hj
      · rw [v₂, u₁.gpr, st _ (by omega_arith)]
    · rw [m₂, scr_loc hp (by omega_arith) ho, u₁.mem]; exact st o ho
    · rw [o₂ _ he (by omega_arith), lw_mem u₁.mem]; exact lt e he (by omega_arith)

end

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- `finish`'s first block: the count, for `finalize`. -/
theorem fiA_ok {data : List Byte} {s : State} (h : HI s₀ data s) :
    WP isa (.block [.mov .ecx (Impl.Argon2.X86.Derive.fr countLoOff),
      .mov .edx (Impl.Argon2.X86.Derive.fr countHiOff)]) s fun t => HI s₀ data t ∧
      t.gpr .ecx = BitVec.ofNat 32 data.length ∧ t.gpr .edx = BitVec.ofNat 32 (data.length / 2 ^ 32) := by
  simp only [Impl.Argon2.X86.Derive.fr]
  refine wp_ldloc hp h.inv (d := countLoOff) (by decide) fun s₁ u₁ =>
    wp_ldloc hp (h.inv.upd u₁ (by decide) (by decide)) (d := countHiOff) (by decide) fun s₂ u₂ =>
      WP.block_nil ?_
  obtain m₂ : s₂.mem = s.mem := by rw [u₂.mem, u₁.mem]
  refine ⟨⟨(h.inv.upd u₁ (by decide) (by decide)).upd u₂ (by decide) (by decide), Prm.of_lw h.prm fun d _ => lw_mem m₂ d,
    by rw [u₂.other _ (by decide), u₁.other _ (by decide), h.ebx], by rw [m₂]; exact h.repr,
    by rw [lw_mem m₂]; exact h.lo, by rw [lw_mem m₂]; exact h.hi, h.len⟩,
    by rw [u₂.other _ (by decide), u₁.gpr, h.lo], by rw [u₂.gpr, lw_mem u₁.mem, h.hi]⟩

/-- `finish`'s `finalize`: the digest at `scratch + 768`. -/
theorem fiFin_ok {data : List Byte} {s : State} (h : HI s₀ data s)
    (ecx : s.gpr .ecx = BitVec.ofNat 32 data.length) (edx : s.gpr .edx = BitVec.ofNat 32 (data.length / 2 ^ 32)) :
    WP isa Impl.Argon2.X86.HPrime.finalize s fun t => Inv s₀ t ∧ Prm s₀ t ∧ t.gpr .ebx = scrP s₀ ∧
      bytesAt t.mem ((scrP s₀).setWidth 64 + 768) 64 = Spec.Blake2.finalHash b (Spec.Blake2.init b 64 0) data := by
  have hn := h.len
  refine (finalize_k (ctx hp h.inv h.ebx) (h0 := Spec.Blake2.init b 64 0) h.repr
    (by rw [edx, ecx]; exact count64 (by omega_arith)) (by omega_arith)).mono fun s₃ ⟨dg, k₃⟩ => ?_
  obtain ⟨i₃, l₃⟩ := h.inv.keeps hp k₃
  exact ⟨i₃, Prm.of_lw h.prm fun d hd => l₃ d (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd; rcases hd with rfl | rfl | rfl | rfl <;> decide),
    k₃.ebx.trans h.ebx, dg⟩

/-- `finish`'s copy of the digest to the locals. -/
theorem fiCopy_ok {s : State} {dg : List Byte} (h : Inv s₀ s ∧ Prm s₀ s ∧ s.gpr .ebx = scrP s₀ ∧
      bytesAt s.mem ((scrP s₀).setWidth 64 + 768) 64 = dg) :
    WP isa (.block ((List.range 16).flatMap Impl.Argon2.X86.Derive.copyWord)) s fun t => Inv s₀ t ∧ Prm s₀ t ∧
      bytesAt t.mem ((E s₀).setWidth 64) 64 = dg := by
  have hs := hp.scr_fits
  obtain hE := E_hi hp
  obtain ⟨i₃, pr₃, b₃, dg₃⟩ := h
  refine (copy_ok hp i₃ b₃ 16 (Nat.le_refl _)).mono fun t ⟨it, _, wt, _, lt⟩ =>
    ⟨it, Prm.of_lw pr₃ fun d hd => ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    obtain hd' : 64 ≤ d ∧ d + 4 ≤ 144 := by
      rcases hd with rfl | rfl | rfl | rfl <;> decide
    rw [lt d (by omega_arith) hd'.1]
  · rw [← dg₃]
    refine bytes_of_words (k := 16) fun j hj => ?_
    have := wt j hj
    simp only [lw] at this
    rw [addr_eq (by omega_arith), addr_eq (by omega_arith)] at this
    rw [this, BitVec.add_assoc, show (768 : Addr) = BitVec.ofNat 64 768 from rfl, BitVec.ofNat_add_ofNat]

theorem finish_ok {data : List Byte} {s : State} (h : HI s₀ data s) :
    WP isa Impl.Argon2.X86.Derive.finish s fun t => Inv s₀ t ∧ Prm s₀ t ∧
      bytesAt t.mem ((E s₀).setWidth 64) 64 = Spec.Blake2.finalHash b (Spec.Blake2.init b 64 0) data := by
  unfold Impl.Argon2.X86.Derive.finish
  exact WP.seq ((fiA_ok hp h).mono fun s₂ ⟨h₂, c₂, d₂⟩ => WP.seq ((fiFin_ok hp h₂ c₂ d₂).mono
    fun s₃ h₃ => fiCopy_ok hp h₃))

theorem code_ok {s : State} (h : Inv s₀ s) (pr : Prm s₀ s) :
    WP isa Impl.Argon2.X86.Derive.code s fun t => Inv s₀ t ∧ Prm s₀ t ∧
      bytesAt t.mem ((E s₀).setWidth 64) 64 =
        Spec.Argon2.initialHash (prm s₀) (pwB s₀) (saltB s₀) (secB s₀) (adB s₀) := by
  obtain l1 := (arg s₀ 2).isLt
  obtain l2 := (arg s₀ 4).isLt
  obtain l3 := (arg s₀ 10).isLt
  unfold Impl.Argon2.X86.Derive.code
  refine WP.seq ((start_ok hp h pr).mono fun s₁ h₁ => ?_)
  refine WP.seq ((absorb_ok hp (ptr := 1) (len := 2) (by decide) (by decide) (by simp) hp.pw_fits
    (by rw [Proof.Argon2.initialHeader_length]; omega_arith) h₁).mono fun s₂ h₂ => ?_)
  refine WP.seq ((absorb_ok hp (ptr := 3) (len := 4) (by decide) (by decide) (by simp) hp.salt_fits
    (by simp only [Proof.Argon2.appendInput_length, Proof.Argon2.initialHeader_length, bytesAt,
      List.length_map, List.length_range]; omega_arith) h₂).mono fun s₃ h₃ => ?_)
  refine WP.seq ((absorb_ok hp (ptr := 9) (len := 10) (by decide) (by decide) (by simp) hp.sec_fits
    (by simp only [Proof.Argon2.appendInput_length, Proof.Argon2.initialHeader_length, bytesAt,
      List.length_map, List.length_range]; omega_arith) h₃).mono fun s₄ h₄ => ?_)
  refine WP.seq ((absorb_ok hp (ptr := 11) (len := 12) (by decide) (by decide) (by simp) hp.ad_fits
    (by simp only [Proof.Argon2.appendInput_length, Proof.Argon2.initialHeader_length, bytesAt,
      List.length_map, List.length_range]; omega_arith) h₄).mono fun s₅ h₅ => ?_)
  refine (finish_ok hp h₅).mono fun t ⟨it, pt, bt⟩ => ⟨it, pt, ?_⟩
  rw [bt, Proof.Argon2.initialHash_stream, List.take_of_length_le (by rw [HPrime.finalHash_length])]
  rfl

end

end VG.Proof.Argon2.X86.Derive

end

end

/-! ### `Argon2.X86.Derive.HCall`, which this module and modules that import it used -/

section

/-!
# Argon2 on x86 (32-bit): calls of H′ in the derivation

The derivation calls `vg_argon2_hprime` in a frame of its five arguments,
`hprime(r, eax, edi, ecx, edx)` with `r` the input's pointer (`ebp` for the
first blocks of a lane, `esi` for the tag), from the body (`Inv`).
`hcall_ok` runs one: its input lies in the memory matrix or the locals, its
output in the memory matrix or `out`, and `scratch` is its working space. The
call writes only the output, `scratch` and the 84 bytes below the locals.
-/

@[expose] public section

namespace VG.Proof.Argon2.X86.Derive

open VG VG.X86
open VG.Spec.Blake2 (bytesAt)

theorem hPrime_nosp : NoSp Impl.Argon2.X86.HPrime.code := NoSp.of_all (by lit_decide)
theorem hPrime_stack : stackUse Impl.Argon2.X86.HPrime.code = 60 := by lit_decide

/-- The bytes of a region a frame's regions miss are kept. -/
theorem bytes_keep {rs : List Region} {m m' : Mem} (f : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, n⟩ r) (hR : n ≤ 2 ^ 64) :
    bytesAt m' p n = bytesAt m p n :=
  Proof.Blake2.bytesAt_congr fun _ hi => f.bytes (R := ⟨p, n⟩) hd hR hi

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- A range of the 84 bytes below the locals. -/
theorem in_call {x : BitVec 32} {n : Nat} (h₁ : (E s₀).toNat ≤ x.toNat + 84)
    (h₂ : x.toNat + n ≤ (E s₀).toNat) : Region.Sub ⟨x.setWidth 64, n⟩ (callR s₀) := by
  obtain hE := E_nat hp
  have := hp.esp_lo
  exact sub32 (by rw [sub_nat (by omega_using [hE, this])]; omega_using [h₁]) (by rw [sub_nat (by omega_using [hE, this])]; omega_using [h₂])

theorem call_disj {R : Region} (hR : R ∈ [memR s₀, scrR s₀, outR s₀]) : (callR s₀).Disjoint R :=
  (hp.stk_all R (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR ⊢
    rcases hR with h | h | h <;> simp [h])).sub_left (call_stk hp)

theorem loc_call : (locR s₀).Disjoint (callR s₀) := by
  obtain hE := E_nat hp
  have := hp.esp_lo
  have := E_hi hp
  exact disj32 (.inr (by rw [sub_nat (by omega_arith)]; omega_arith)) (by omega_arith) (by rw [sub_nat (by omega_arith)]; omega_using [])

theorem loc_sub_stk : Region.Sub (locR s₀) (stkR s₀) := by
  simpa using frame_stk hp (d := 0) (n := 144) (by decide)

theorem loc_disj' {R : Region} (hR : R ∈ [memR s₀, scrR s₀, outR s₀]) : (locR s₀).Disjoint R :=
  (hp.stk_all R (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR ⊢
    rcases hR with h | h | h <;> simp [h])).sub_left (loc_sub_stk hp)

/-- What H′ needs, from the body: `hprime(r, eax, edi, ecx, edx)`. -/
theorem hcall_pre {s : State} (h : Inv s₀ s) {r : Reg} (hr : r ≠ .esp)
    (hdx : s.gpr .edx = scrP s₀)
    (hin : ∃ R ∈ [memR s₀, locR s₀], ∃ off, (s.gpr r).setWidth 64 = R.base + BitVec.ofNat 64 off ∧
      off + (s.gpr .eax).toNat ≤ R.len)
    (hinfit : (s.gpr r).toNat + (s.gpr .eax).toNat ≤ 2 ^ 32)
    (hout : ∃ R ∈ [memR s₀, outR s₀], ∃ off, (s.gpr .edi).setWidth 64 = R.base + BitVec.ofNat 64 off ∧
      off + (s.gpr .ecx).toNat ≤ R.len)
    (houtfit : (s.gpr .edi).toNat + (s.gpr .ecx).toNat ≤ 2 ^ 32)
    (hL : 1 ≤ (s.gpr .ecx).toNat) :
    CallPre HPrime.hPrimeX86 [.edx, .ecx, .edi, .eax, r]
      [⟨(s.gpr r).setWidth 64, (s.gpr .eax).toNat⟩, ⟨(s.gpr .esp - BitVec.ofNat 32 20).setWidth 64, 20⟩]
      [⟨(s.gpr .edi).setWidth 64, (s.gpr .ecx).toNat⟩, scrR s₀] s := by
  obtain hE := E_nat hp
  have hlo := hp.esp_lo
  obtain hhi := E_hi hp
  have hs := hp.scr_fits
  have esp := h.esp
  obtain nesp : Reg.esp ∉ [Reg.edx, .ecx, .edi, .eax, r] := by simp [Ne.symm hr]
  obtain fit : 4 * [Reg.edx, .ecx, .edi, .eax, r].length + 4 ≤ (s.gpr .esp).toNat := by
    simp only [List.length_cons, List.length_nil]; rw [esp]; omega_using [hE, hlo]
  obtain a0 := callEntry_arg fit nesp (i := 0) (by simp)
  obtain a1 := callEntry_arg fit nesp (i := 1) (by simp)
  obtain a2 := callEntry_arg fit nesp (i := 2) (by simp)
  obtain a3 := callEntry_arg fit nesp (i := 3) (by simp)
  obtain a4 := callEntry_arg fit nesp (i := 4) (by simp)
  simp only [List.length_cons, List.length_nil, List.getElem_cons_succ, List.getElem_cons_zero,
    Nat.reduceAdd, Nat.reduceSub] at a0 a1 a2 a3 a4
  rw [hdx] at a4
  -- The input and the output.
  obtain ⟨RI, hRI, oI, bI, lI⟩ := hin
  obtain ⟨RO, hRO, oO, bO, lO⟩ := hout
  obtain sI : Region.Sub ⟨(s.gpr r).setWidth 64, (s.gpr .eax).toNat⟩ RI := by
    rw [bI]; exact Offset.sub_base _ lI
  obtain sO : Region.Sub ⟨(s.gpr .edi).setWidth 64, (s.gpr .ecx).toNat⟩ RO := by
    rw [bO]; exact Offset.sub_base _ lO
  obtain inW : RI ∈ s.wr := by
    rw [h.wr]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hRI
    rcases hRI with rfl | rfl
    · exact mem_mem hp
    · exact loc_mem s₀
  obtain outW : RO ∈ s.wr := by
    rw [h.wr]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hRO
    rcases hRO with rfl | rfl
    · exact mem_mem hp
    · exact out_mem hp
  obtain cI : Covers [⟨(s.gpr r).setWidth 64, (s.gpr .eax).toNat⟩] s.wr :=
    Covers.of_sub fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact ⟨RI, inW, oI, bI, lI⟩
  obtain cO : Covers [⟨(s.gpr .edi).setWidth 64, (s.gpr .ecx).toNat⟩] s.wr :=
    Covers.of_sub fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact ⟨RO, outW, oO, bO, lO⟩
  obtain scrW : scrR s₀ ∈ s.wr := by rw [h.wr]; exact scr_mem hp
  obtain I_scr : Region.Disjoint ⟨(s.gpr r).setWidth 64, (s.gpr .eax).toNat⟩ (scrR s₀) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hRI
    rcases hRI with rfl | rfl
    · exact hp.mem_scr.sub_left sI
    · exact (loc_disj' hp (R := scrR s₀) (by simp)).sub_left sI
  obtain I_call : Region.Disjoint ⟨(s.gpr r).setWidth 64, (s.gpr .eax).toNat⟩ (callR s₀) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hRI
    rcases hRI with rfl | rfl
    · exact (call_disj hp (R := memR s₀) (by simp)).symm.sub_left sI
    · exact (loc_call hp).sub_left sI
  obtain O_scr : Region.Disjoint ⟨(s.gpr .edi).setWidth 64, (s.gpr .ecx).toNat⟩ (scrR s₀) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hRO
    rcases hRO with rfl | rfl
    · exact hp.mem_scr.sub_left sO
    · exact hp.scr_out.symm.sub_left sO
  obtain O_call : Region.Disjoint ⟨(s.gpr .edi).setWidth 64, (s.gpr .ecx).toNat⟩ (callR s₀) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hRO
    rcases hRO with rfl | rfl
    · exact (call_disj hp (R := memR s₀) (by simp)).symm.sub_left sO
    · exact (call_disj hp (R := outR s₀) (by simp)).symm.sub_left sO
  obtain S_call : (scrR s₀).Disjoint (callR s₀) := (call_disj hp (R := scrR s₀) (by simp)).symm
  -- The callee's stack, arguments and return address.
  obtain e20 : (s.gpr .esp - BitVec.ofNat 32 20).toNat = (E s₀).toNat - 20 := by rw [esp, sub_nat (by omega_using [hE, hlo])]
  obtain e24 : (s.gpr .esp - BitVec.ofNat 32 24).toNat = (E s₀).toNat - 24 := by rw [esp, sub_nat (by omega_using [hE, hlo])]
  obtain e84 : (s.gpr .esp - BitVec.ofNat 32 24 - BitVec.ofNat 32 60).toNat = (E s₀).toNat - 84 := by
    rw [sub_nat (by omega_using [hE, hlo, e24]), e24]; omega_using []
  obtain cA : Region.Sub ⟨(s.gpr .esp - BitVec.ofNat 32 20).setWidth 64, 20⟩ (callR s₀) :=
    in_call hp (by omega_using [e20]) (by omega_using [hE, hlo, e20])
  obtain cR : Region.Sub ⟨(s.gpr .esp - BitVec.ofNat 32 24).setWidth 64, 4⟩ (callR s₀) :=
    in_call hp (by omega_using [e24]) (by omega_using [hE, hlo, e24])
  obtain cS : Region.Sub (below (s.gpr .esp - BitVec.ofNat 32 24) 60) (callR s₀) :=
    in_call hp (by omega_using [e84]) (by omega_using [hE, hlo, e84])
  obtain a20 : argAddr (pushed [Reg.edx, .ecx, .edi, .eax, r] s).callEntry 0 =
      (s.gpr .esp - BitVec.ofNat 32 20).setWidth 64 := callEntry_argAddr0 _ _
  obtain ce : (pushed [Reg.edx, .ecx, .edi, .eax, r] s).callEntry.gpr .esp = s.gpr .esp - BitVec.ofNat 32 24 :=
    callEntry_esp' _ _
  refine ⟨?_, ?_, ?_⟩
  · simp only [HPrime.hPrimeX86, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr, arg_withRegions,
      argAddr_withRegions, a0, a1, a2, a3, a4, a20, ce]
    refine ⟨trivial, trivial, I_scr, O_scr, ?_, ?_,
      ?_, ?_,
      I_call.symm.sub_left cS, O_call.symm.sub_left cS, S_call.symm.sub_left cS, hinfit, houtfit,
      by omega_using [hs], by rw [sub_nat (by rw [esp]; omega_using [hE, hlo]), esp]; omega_using [hE, hlo], by rw [sub_nat (by rw [esp]; omega_using [hE, hlo]), esp]; omega_using [],
      hL⟩
    · exact O_call.symm.sub_left cA
    · exact S_call.symm.sub_left cA
    · exact O_call.symm.sub_left cR
    · exact S_call.symm.sub_left cR
  · intro a n ⟨q, hq, hc⟩
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · obtain ⟨q', hq', hc'⟩ := cI a n ⟨_, List.mem_singleton_self _, hc⟩
      exact InRegions_append_cons.mpr (.inr ⟨q', List.mem_append_right _ hq', hc'⟩)
    · exact InRegions_append_cons.mpr (.inl (by simpa using hc))
    · obtain ⟨q', hq', hc'⟩ := cO a n ⟨_, List.mem_singleton_self _, hc⟩
      exact InRegions_append_cons.mpr (.inr ⟨q', List.mem_append_right _ hq', hc'⟩)
    · exact InRegions_append_cons.mpr (.inr ⟨_, List.mem_append_right _ scrW, hc⟩)
  · intro a n ⟨q, hq, hc⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · obtain ⟨q', hq', hc'⟩ := cO a n ⟨_, List.mem_singleton_self _, hc⟩
      exact ⟨q', List.mem_cons_of_mem _ hq', hc'⟩
    · exact ⟨_, List.mem_cons_of_mem _ scrW, hc⟩

/-- A call of H′ from the body: `hprime(r, eax, edi, ecx, edx)`. -/
theorem hcall_ok {s : State} (h : Inv s₀ s) {r : Reg} (hr : r ≠ .esp)
    (hdx : s.gpr .edx = scrP s₀)
    (hin : ∃ R ∈ [memR s₀, locR s₀], ∃ off, (s.gpr r).setWidth 64 = R.base + BitVec.ofNat 64 off ∧
      off + (s.gpr .eax).toNat ≤ R.len)
    (hinfit : (s.gpr r).toNat + (s.gpr .eax).toNat ≤ 2 ^ 32)
    (hout : ∃ R ∈ [memR s₀, outR s₀], ∃ off, (s.gpr .edi).setWidth 64 = R.base + BitVec.ofNat 64 off ∧
      off + (s.gpr .ecx).toNat ≤ R.len)
    (houtfit : (s.gpr .edi).toNat + (s.gpr .ecx).toNat ≤ 2 ^ 32)
    (hL : 1 ≤ (s.gpr .ecx).toNat) {Q : State → Prop}
    (k : ∀ t, Inv s₀ t → (∀ q ∈ calleeSaved, t.gpr q = s.gpr q) →
      Frame [⟨(s.gpr .edi).setWidth 64, (s.gpr .ecx).toNat⟩, scrR s₀, callR s₀] s.mem t.mem →
      bytesAt t.mem ((s.gpr .edi).setWidth 64) (s.gpr .ecx).toNat =
        Spec.Argon2.hPrime (s.gpr .ecx).toNat
          (bytesAt s.mem ((s.gpr r).setWidth 64) (s.gpr .eax).toNat) → Q t) :
    WP isa (.frame (.push [.edx, .ecx, .edi, .eax, r]) (.call Impl.Argon2.X86.Derive.hPrimeName
      Impl.Argon2.X86.HPrime.code) (.pop .eax 5)) s Q := by
  obtain hE := E_nat hp
  have hlo := hp.esp_lo
  obtain hhi := E_hi hp
  have hs := hp.scr_fits
  have esp := h.esp
  obtain nesp : Reg.esp ∉ [Reg.edx, .ecx, .edi, .eax, r] := by simp [Ne.symm hr]
  obtain fit : 4 * [Reg.edx, .ecx, .edi, .eax, r].length + 4 ≤ (s.gpr .esp).toNat := by
    simp only [List.length_cons, List.length_nil]; rw [esp]; omega_using [hE, hlo]
  obtain a0 := callEntry_arg fit nesp (i := 0) (by simp)
  obtain a1 := callEntry_arg fit nesp (i := 1) (by simp)
  obtain a2 := callEntry_arg fit nesp (i := 2) (by simp)
  obtain a3 := callEntry_arg fit nesp (i := 3) (by simp)
  obtain a4 := callEntry_arg fit nesp (i := 4) (by simp)
  simp only [List.length_cons, List.length_nil, List.getElem_cons_succ, List.getElem_cons_zero,
    Nat.reduceAdd, Nat.reduceSub] at a0 a1 a2 a3 a4
  rw [hdx] at a4
  -- The input and the output.
  obtain ⟨RI, hRI, oI, bI, lI⟩ := hin
  obtain ⟨RO, hRO, oO, bO, lO⟩ := hout
  obtain sI : Region.Sub ⟨(s.gpr r).setWidth 64, (s.gpr .eax).toNat⟩ RI := by
    rw [bI]; exact Offset.sub_base _ lI
  obtain sO : Region.Sub ⟨(s.gpr .edi).setWidth 64, (s.gpr .ecx).toNat⟩ RO := by
    rw [bO]; exact Offset.sub_base _ lO
  obtain inW : RI ∈ s.wr := by
    rw [h.wr]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hRI
    rcases hRI with rfl | rfl
    · exact mem_mem hp
    · exact loc_mem s₀
  obtain outW : RO ∈ s.wr := by
    rw [h.wr]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hRO
    rcases hRO with rfl | rfl
    · exact mem_mem hp
    · exact out_mem hp
  obtain cI : Covers [⟨(s.gpr r).setWidth 64, (s.gpr .eax).toNat⟩] s.wr :=
    Covers.of_sub fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact ⟨RI, inW, oI, bI, lI⟩
  obtain cO : Covers [⟨(s.gpr .edi).setWidth 64, (s.gpr .ecx).toNat⟩] s.wr :=
    Covers.of_sub fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact ⟨RO, outW, oO, bO, lO⟩
  obtain scrW : scrR s₀ ∈ s.wr := by rw [h.wr]; exact scr_mem hp
  obtain I_scr : Region.Disjoint ⟨(s.gpr r).setWidth 64, (s.gpr .eax).toNat⟩ (scrR s₀) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hRI
    rcases hRI with rfl | rfl
    · exact hp.mem_scr.sub_left sI
    · exact (loc_disj' hp (R := scrR s₀) (by simp)).sub_left sI
  obtain I_call : Region.Disjoint ⟨(s.gpr r).setWidth 64, (s.gpr .eax).toNat⟩ (callR s₀) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hRI
    rcases hRI with rfl | rfl
    · exact (call_disj hp (R := memR s₀) (by simp)).symm.sub_left sI
    · exact (loc_call hp).sub_left sI
  obtain O_scr : Region.Disjoint ⟨(s.gpr .edi).setWidth 64, (s.gpr .ecx).toNat⟩ (scrR s₀) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hRO
    rcases hRO with rfl | rfl
    · exact hp.mem_scr.sub_left sO
    · exact hp.scr_out.symm.sub_left sO
  obtain O_call : Region.Disjoint ⟨(s.gpr .edi).setWidth 64, (s.gpr .ecx).toNat⟩ (callR s₀) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hRO
    rcases hRO with rfl | rfl
    · exact (call_disj hp (R := memR s₀) (by simp)).symm.sub_left sO
    · exact (call_disj hp (R := outR s₀) (by simp)).symm.sub_left sO
  obtain S_call : (scrR s₀).Disjoint (callR s₀) := (call_disj hp (R := scrR s₀) (by simp)).symm
  -- The callee's stack, arguments and return address.
  obtain e20 : (s.gpr .esp - BitVec.ofNat 32 20).toNat = (E s₀).toNat - 20 := by rw [esp, sub_nat (by omega_using [hE, hlo])]
  obtain e24 : (s.gpr .esp - BitVec.ofNat 32 24).toNat = (E s₀).toNat - 24 := by rw [esp, sub_nat (by omega_using [hE, hlo])]
  obtain e84 : (s.gpr .esp - BitVec.ofNat 32 24 - BitVec.ofNat 32 60).toNat = (E s₀).toNat - 84 := by
    rw [sub_nat (by omega_using [hE, hlo, e24]), e24]; omega_using []
  obtain cA : Region.Sub ⟨(s.gpr .esp - BitVec.ofNat 32 20).setWidth 64, 20⟩ (callR s₀) :=
    in_call hp (by omega_using [e20]) (by omega_using [hE, hlo, e20])
  obtain cR : Region.Sub ⟨(s.gpr .esp - BitVec.ofNat 32 24).setWidth 64, 4⟩ (callR s₀) :=
    in_call hp (by omega_using [e24]) (by omega_using [hE, hlo, e24])
  obtain cS : Region.Sub (below (s.gpr .esp - BitVec.ofNat 32 24) 60) (callR s₀) :=
    in_call hp (by omega_using [e84]) (by omega_using [hE, hlo, e84])
  obtain a20 : argAddr (pushed [Reg.edx, .ecx, .edi, .eax, r] s).callEntry 0 =
      (s.gpr .esp - BitVec.ofNat 32 20).setWidth 64 := callEntry_argAddr0 _ _
  obtain ce : (pushed [Reg.edx, .ecx, .edi, .eax, r] s).callEntry.gpr .esp = s.gpr .esp - BitVec.ofNat 32 24 :=
    callEntry_esp' _ _
  obtain pre := hcall_pre hp h hr hdx ⟨RI, hRI, oI, bI, lI⟩ hinfit ⟨RO, hRO, oO, bO, lO⟩ houtfit hL
  refine WP.callWith HPrime.hPrime_verified.1 hPrime_nosp (by simp) nesp
    (by rw [hPrime_stack, esp]; simp only [List.length_cons, List.length_nil]; omega_using [hE, hlo]) pre
    fun t rd' wr' cs' f' ⟨s₂, m₂, post⟩ => ?_
  simp only [HPrime.hPrimeX86, arg_withRegions, State.withRegions_mem, a0, a1, a2, a3] at post
  obtain cB : Region.Sub (below (s.gpr .esp) 24) (callR s₀) := in_call hp (by rw [e24]; omega_using []) (by rw [e24]; omega_using [hE, hlo])
  obtain cf := callEntry_frame fit nesp
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul, Nat.zero_add] at cf
  rw [hPrime_stack] at f'
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul, Nat.zero_add] at f'
  obtain bk : bytesAt (pushed [Reg.edx, .ecx, .edi, .eax, r] s).callEntry.mem ((s.gpr r).setWidth 64)
      (s.gpr .eax).toNat = bytesAt s.mem ((s.gpr r).setWidth 64) (s.gpr .eax).toNat :=
    bytes_keep cf
    (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq
      exact I_call.sub_right cB)
    (Nat.le_of_lt (Nat.lt_trans (s.gpr .eax).isLt (by decide)))
  obtain m₂ : Frame [below (s.gpr .esp) 24] s₂.mem t.mem :=
    Frame.below_mono (wr := []) m₂ (by simp only [List.length_cons, List.length_nil]; omega_using [])
      (by rw [esp]; omega_using [hE, hlo])
  rw [bk, ← bytes_keep m₂ (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq
      exact O_call.sub_right cB)
    (Nat.le_of_lt (Nat.lt_trans (s.gpr .ecx).isLt (by decide)))] at post
  obtain f₁ : Frame [⟨(s.gpr .edi).setWidth 64, (s.gpr .ecx).toNat⟩, scrR s₀, callR s₀] s.mem t.mem :=
    f'.sub fun q hq => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩
      · refine ⟨callR s₀, by simp, ?_⟩
        rw [esp]
        exact fun _ h => h
  refine k t (h.step (cs' .esp (by decide)) (cs' .ebp (by decide)) rd' wr' (f₁.sub fun q hq => ?_)) cs' f₁ post
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · refine ⟨RO, ?_, sO⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hRO
    rcases hRO with rfl | rfl <;> simp
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, fun _ h => h⟩

end

end VG.Proof.Argon2.X86.Derive

end

end

@[expose] public section

section

/-!
# Argon2 on x86 (32-bit): clearing the memory matrix

`clear_ok`: `clear` zeroes the `blocks · 1024` bytes of the memory matrix,
one word per iteration, and writes nothing else. Its loop counts the words
left in `ecx` (`blocks · 256`, by eight doublings), with `edi` the next
word's address.
-/

namespace VG.Proof.Argon2.X86.Derive

open VG VG.X86
open VG.X86.Wp (Upd Mupd wp_movi wp_mov wp_add wp_addi wp_subi)
open VG.Spec.Blake2 (bytesAt)

/-- The memory matrix, as an address. -/
abbrev memB (s₀ : State) : Addr := (memP s₀).setWidth 64

/-- A byte after a zero word is stored at `a`. -/
theorem writeW_zero (m : Mem) (a x : Addr) :
    (m.writeW a (0 : BitVec 32)) x = if (x - a).toNat < 4 then 0 else m x := by
  simp only [Mem.writeW, Mem.write]
  split <;> simp

/-- `[x + d + k]`, at a 32-bit address that does not wrap. -/
theorem addr32 {x : BitVec 32} {d k : Nat} (h : x.toNat + d + k < 2 ^ 32) :
    addr (x + BitVec.ofNat 32 d) k = x.setWidth 64 + BitVec.ofNat 64 (d + k) := by
  rw [addr_eq (by rw [add_nat (by omega_arith)]; omega_arith), HPrime.setWidth_add (by omega_arith), BitVec.add_assoc,
    BitVec.ofNat_add_ofNat]

/-- A store to a region the body may write keeps the invariant. -/
theorem Inv.store {s₀ s t : State} (h : Inv s₀ s) {R : Region} (hR : R ∈ bodyW s₀) {a : Addr}
    {v : BitVec 32} (hc : R.Contains a 4) (u : Mupd s t (s.mem.writeW a v)) : Inv s₀ t :=
  h.step (by rw [u.gpr]) (by rw [u.gpr]) u.rd u.wr (by rw [u.mem]; exact (Frame.refl _ _).writeW hR v hc)

/-- `cmp d, [b + o]`, and the borrow. -/
theorem wp_cmpm {s : State} {is : List Instr} {Q : State → Prop} {d b : Reg} {B : BitVec 32} {o : Nat}
    (hb : s.gpr b = B) (hin : InRegions (s.rd ++ s.wr) (addr B o) 4)
    (k : ∀ s', Wp.Fupd s s' → s'.cf = some (decide ((s.gpr d).toNat < (s.mem.readW (addr B o) 32).toNat)) →
      s'.zf = some (s.gpr d - s.mem.readW (addr B o) 32 == 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .cmp d (.mem ⟨b, o⟩) :: is)) s Q :=
  Wp.cons (s' := arithFlags s (s.gpr d - s.mem.readW (addr B o) 32)
      (decide ((s.gpr d).toNat < (s.mem.readW (addr B o) 32).toNat))
      (subOverflow (s.gpr d) (s.mem.readW (addr B o) 32) (s.gpr d - s.mem.readW (addr B o) 32)))
    (by simp only [exec, execAlu, Wp.readSrc_mem hb hin, Option.bind_some])
    (k _ ⟨rfl, rfl, rfl, rfl, rfl⟩ rfl rfl)

/-- `clearWordAt r`'s loop after `j` of the `n` words from `X`, from `s₁`. -/
structure CI (s₀ s₁ : State) (r : Reg) (X : BitVec 32) (n j : Nat) (s : State) : Prop where
  inv : Inv s₀ s
  ptr : s.gpr r = X + BitVec.ofNat 32 (4 * j)
  ecx : s.gpr .ecx = BitVec.ofNat 32 (n - j)
  eax : s.gpr .eax = 0
  oth : ∀ q, q ≠ .eax → q ≠ .ecx → q ≠ r → s.gpr q = s₁.gpr q
  zero : ∀ i < 4 * j, s.mem (X.setWidth 64 + BitVec.ofNat 64 i) = 0
  frame : Frame [⟨X.setWidth 64, 4 * n⟩] s₁.mem s.mem

section
variable {s₀ : State} (hp : DPre s₀)
include hp

theorem blocks_pos : 1 ≤ blocksN s₀ := by
  rw [hp.blocks_eq, hp.laneLen_eq]
  have := Nat.mul_le_mul hp.lanes_pos (show 1 ≤ 4 * (prm s₀).segmentLen by have := hp.segLen_two; omega_arith)
  omega_arith

omit hp in
/-- `n` words zeroed from `X`, within a region `R` the body may write. -/
theorem clearLoop_ok {r : Reg} (hra : r ≠ .eax) (hrc : r ≠ .ecx) (hrs : r ≠ .esp) (hrb : r ≠ .ebp)
    {X : BitVec 32} {n : Nat} {R : Region} (hR : R ∈ bodyW s₀) (hRw : R ∈ (entry s₀).wr) {off : Nat}
    (hRX : X.setWidth 64 = R.base + BitVec.ofNat 64 off) (hRn : off + 4 * n ≤ R.len) (hR64 : R.len < 2 ^ 64)
    (hX : X.toNat + 4 * n ≤ 2 ^ 32) (hn : 1 ≤ n) {s₁ : State} (h : CI s₀ s₁ r X n 0 s₁) :
    WP isa (.loop (.block (Impl.Argon2.X86.Derive.clearWordAt r)) .ne) s₁ (CI s₀ s₁ r X n n) := by
  refine WP.loop (M := isa) (fun m s => ∃ j, m = n - j ∧ j < n ∧ CI s₀ s₁ r X n j s)
    ?_ n s₁ ⟨0, by omega_arith, by omega_arith, h⟩
  rintro m s ⟨j, rfl, hj, c⟩
  obtain ea : addr (s.gpr r) 0 = X.setWidth 64 + BitVec.ofNat 64 (4 * j) := by
    rw [c.ptr, addr32 (by omega_arith), Nat.add_zero]
  obtain hc : R.Contains (addr (s.gpr r) 0) 4 := by
    rw [ea, hRX, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    exact Offset.contains_base (k := R.len) _ (by omega_arith) (by omega_arith)
  obtain hcX : (⟨X.setWidth 64, 4 * n⟩ : Region).Contains (addr (s.gpr r) 0) 4 := by
    rw [ea]; exact Offset.contains_base _ (by omega_arith) (by omega_arith)
  simp only [Impl.Argon2.X86.Derive.clearWordAt]
  refine Wp.wp_stm rfl (by rw [c.inv.wr]; exact ⟨_, hRw, hc⟩) fun t₁ u₁ => ?_
  obtain i₁ := c.inv.store hR hc u₁
  refine wp_addi fun t₂ u₂ => wp_subi fun t u _ zf => WP.block_nil ?_
  obtain i₃ := (i₁.upd u₂ hrs hrb).upd u (by decide) (by decide)
  obtain e₁ : t.gpr .ecx = BitVec.ofNat 32 (n - (j + 1)) := by
    rw [u.gpr, u₂.other _ hrc.symm, u₁.gpr, c.ecx, Wp.ofNat_pred (by omega_arith)]; rfl
  obtain next : CI s₀ s₁ r X n (j + 1) t := by
    refine ⟨i₃, ?_, e₁, ?_, fun q a b d => ?_, fun i hi => ?_, ?_⟩
    · rw [u.other _ hrc, u₂.gpr, u₁.gpr, c.ptr, show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl,
        BitVec.add_assoc, BitVec.ofNat_add_ofNat]; rfl
    · rw [u.other _ (by decide), u₂.other _ hra.symm, u₁.gpr, c.eax]
    · rw [u.other _ b, u₂.other _ d, u₁.gpr, c.oth q a b d]
    · rw [u.mem, u₂.mem, u₁.mem, c.eax, ea, writeW_zero]
      by_cases hi' : i < 4 * j
      · split
        · rfl
        · exact c.zero i hi'
      · rw [show X.setWidth 64 + BitVec.ofNat 64 i = X.setWidth 64 + BitVec.ofNat 64 (4 * j) +
          BitVec.ofNat 64 (i - 4 * j) by
          rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.add_sub_cancel' (by omega_arith)],
          Offset.add_sub_cancel_left]
        split
        · rfl
        · rename_i hn; rw [BitVec.toNat_ofNat] at hn; omega_arith
    · rw [u.mem, u₂.mem, u₁.mem]
      exact c.frame.writeW (List.mem_singleton_self _) _ hcX
  obtain z : t.zf = some (decide (n - (j + 1) = 0)) := by
    rw [zf, u₂.other _ hrc.symm, u₁.gpr, c.ecx, Wp.ofNat_pred (by omega_arith), Wp.ofNat_beq_zero (by omega_arith)]
    rfl
  by_cases done : j + 1 = n
  · refine .inl ⟨?_, done ▸ next⟩
    simp only [eval, z, show n - (j + 1) = 0 by omega_arith, decide_true, Option.map_some, Bool.not_true]
  · refine .inr ⟨?_, n - (j + 1), by omega_arith, j + 1, rfl, by omega_arith, next⟩
    simp only [eval, z, show n - (j + 1) ≠ 0 by omega_arith, decide_false, Option.map_some, Bool.not_false]

theorem clear_ok {s : State} (h : Inv s₀ s) :
    WP isa Impl.Argon2.X86.Derive.clear s fun t => Inv s₀ t ∧ Frame [memR s₀] s.mem t.mem ∧
      ∀ i < blocksN s₀ * 1024, t.mem (memB s₀ + BitVec.ofNat 64 i) = 0 := by
  have hb := hp.blocks_lt
  have hm := hp.mem_fits
  obtain b1 := blocks_pos hp
  have eb : blocksN s₀ = (arg s₀ 14).toNat := rfl
  unfold Impl.Argon2.X86.Derive.clear Impl.Argon2.X86.Derive.clearSetup
  simp only [List.cons_append]
  refine WP.seq (wp_ldarg hp h (i := 13) (by decide) fun s₁ u₁ =>
    wp_ldarg hp (h.upd u₁ (by decide) (by decide)) (i := 14) (by decide) fun s₂ u₂ => ?_)
  obtain i₂ := (h.upd u₁ (by decide) (by decide)).upd u₂ (by decide) (by decide)
  refine dbl_ok 8 (by rw [u₂.gpr]; omega_arith) fun s₃ e₃ k₃ => wp_movi fun s₄ u₄ => WP.block_nil ?_
  obtain i₄ := (i₂.keep k₃).upd u₄ (by decide) (by decide)
  obtain e4 : (4 * (blocksN s₀ * 256)) = blocksN s₀ * 1024 := by omega_arith
  refine (clearLoop_ok (r := .edi) (by decide) (by decide) (by decide) (by decide) (X := memP s₀) (n := blocksN s₀ * 256) (R := memR s₀) (by simp) (mem_mem hp) (off := 0)
      (BitVec.add_zero _).symm (show 0 + 4 * (blocksN s₀ * 256) ≤ blocksN s₀ * 1024 by omega_arith)
      (show blocksN s₀ * 1024 < 2 ^ 64 by omega_arith) (by omega_arith) (by omega_arith)
      ⟨i₄, ?_, ?_, u₄.gpr, fun _ _ _ _ => rfl, fun i hi => absurd hi (by omega_arith), Frame.refl _ _⟩).mono
    fun t c => ⟨c.inv, ?_, fun i hi => c.zero i (by omega_arith)⟩
  · rw [u₄.other _ (by decide), k₃.other _ (by decide) (by decide) (by decide), u₂.other _ (by decide), u₁.gpr]
    simp
  · rw [u₄.other _ (by decide)]
    apply BitVec.eq_of_toNat_eq
    rw [e₃, u₂.gpr, Wp.toNat_ofNat_lt (by omega_arith)]
    omega_arith
  · rw [show s.mem = s₄.mem by rw [u₄.mem, k₃.mem, u₂.mem, u₁.mem]]
    have f := c.frame
    rw [e4] at f
    exact f

omit hp in
/-- `zeroWords r n` from `r = X`, within a region `R` the body may write. -/
theorem zeroWords_ok {s : State} (h : Inv s₀ s) {r : Reg} (hra : r ≠ .eax) (hrc : r ≠ .ecx) (hrs : r ≠ .esp)
    (hrb : r ≠ .ebp) {X : BitVec 32} {n : Nat} {R : Region} (hR : R ∈ bodyW s₀) (hRw : R ∈ (entry s₀).wr)
    {off : Nat} (hRX : X.setWidth 64 = R.base + BitVec.ofNat 64 off) (hRn : off + 4 * n ≤ R.len)
    (hR64 : R.len < 2 ^ 64) (hX : X.toNat + 4 * n ≤ 2 ^ 32) (hn : 1 ≤ n) (hptr : s.gpr r = X) :
    WP isa (Impl.Argon2.X86.Derive.zeroWords r n) s fun t => Inv s₀ t ∧
      (∀ q, q ≠ .eax → q ≠ .ecx → q ≠ r → t.gpr q = s.gpr q) ∧
      Frame [⟨X.setWidth 64, 4 * n⟩] s.mem t.mem ∧ ∀ i < 4 * n, t.mem (X.setWidth 64 + BitVec.ofNat 64 i) = 0 := by
  unfold Impl.Argon2.X86.Derive.zeroWords
  refine WP.seq (wp_movi fun s₁ u₁ => wp_movi fun s₂ u₂ => WP.block_nil ?_)
  obtain i₂ := (h.upd u₁ (by decide) (by decide)).upd u₂ (by decide) (by decide)
  obtain m₂ : s₂.mem = s.mem := by rw [u₂.mem, u₁.mem]
  refine (clearLoop_ok hra hrc hrs hrb hR hRw hRX hRn hR64 hX hn ⟨i₂, ?_, ?_, ?_, fun _ _ _ _ => rfl,
      fun i hi => absurd hi (by omega_arith), Frame.refl _ _⟩).mono fun t c => ⟨c.inv, fun q a b d => ?_, ?_, c.zero⟩
  · rw [u₂.other _ hrc, u₁.other _ hra, hptr]; simp
  · rw [u₂.gpr, Nat.sub_zero]
  · rw [u₂.other _ (by decide), u₁.gpr]
  · rw [c.oth q a b d, u₂.other _ b, u₁.other _ a]
  · rw [← m₂]; exact c.frame

end

end VG.Proof.Argon2.X86.Derive

end

/-!
# Argon2 on x86 (32-bit): the memory's initialization

`memoryInit_ok`: after `memoryInit`, the memory matrix represents
`initMemory` (`Proof.Argon2.Represents`). The matrix is cleared, then each
lane's first two blocks are H′ of the 72 bytes at the start of the locals
(`initBlock_ok`), H₀ followed by the column and the lane, written there just
before the call. `LI s₀ h0 l` is the state after `l` lanes (`initCell`).
-/

namespace VG.Proof.Argon2.X86.Derive

open VG VG.X86
open VG.X86.Wp (Upd Mupd wp_movi wp_mov wp_add wp_addi wp_subi)
open VG.Spec.Blake2 (bytesAt)
open VG.Spec.Argon2 (Block zeroBlock parseBlock)

/-! ## Blocks in memory -/

/-- A block outside a frame's regions is kept. -/
theorem blockAt_keep {rs : List Region} {m m' : Mem} (f : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, 1024⟩ r) : blockAt m' p = blockAt m p := by
  unfold blockAt
  exact congrArg Vector.ofFn (funext fun j => f.read (r := ⟨p, 1024⟩)
    (Offset.contains_base p (by have := j.isLt; omega_arith) (by have := j.isLt; omega_arith)) hd (by decide))

theorem read_zero {m : Mem} {a : Addr} {n : Nat} (h : ∀ i < n, m (a + BitVec.ofNat 64 i) = 0) :
    m.read a n = 0 := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    obtain h0 : m a = 0 := by simpa using h 0 (by omega_arith)
    obtain h1 : m.read (a + 1) n = 0 := ih fun i hi => by
      rw [BitVec.add_assoc, show (1 : Addr) = BitVec.ofNat 64 1 from rfl, BitVec.ofNat_add_ofNat]
      exact h (1 + i) (by omega_arith)
    simp only [Mem.read, h0, h1]
    exact BitVec.zero_append_zero

/-- A block of zero bytes. -/
theorem blockAt_zero {m : Mem} {p : Addr} (h : ∀ i < 1024, m (p + BitVec.ofNat 64 i) = 0) :
    blockAt m p = zeroBlock := by
  unfold blockAt zeroBlock
  apply Vector.ext
  intro j hj
  simp only [Vector.getElem_ofFn, Vector.getElem_replicate]
  exact read_zero fun i hi => by
    rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]; exact h _ (by omega_arith)

/-! ## The initialized cells -/

/-- Cell `k` after the first two blocks of the first `l` lanes are initialized. -/
def initCell (p : Spec.Argon2.Params) (h0 : List Byte) (l k : Nat) : Block :=
  if k / p.laneLen < l ∧ k % p.laneLen < 2 then
    parseBlock (initialBytes h0 (k / p.laneLen) (k % p.laneLen))
  else zeroBlock

theorem initCell_zero (p : Spec.Argon2.Params) (h0 : List Byte) (k : Nat) : initCell p h0 0 k = zeroBlock := by
  unfold initCell
  exact ite_eq_right fun h => Nat.not_lt_zero _ h.1

theorem cell_div {L l c : Nat} (hc : c < L) : (l * L + c) / L = l := by
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega_arith), Nat.div_eq_of_lt hc, Nat.zero_add]

theorem cell_mod {L l c : Nat} (hc : c < L) : (l * L + c) % L = c := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc]

theorem initCell_new (p : Spec.Argon2.Params) (h0 : List Byte) {l c : Nat} (hL : 2 ≤ p.laneLen) (hc : c < 2) :
    initCell p h0 (l + 1) (l * p.laneLen + c) = parseBlock (initialBytes h0 l c) := by
  unfold initCell
  rw [cell_div (by omega_arith), cell_mod (by omega_arith)]
  exact ite_eq_left ⟨by omega_arith, hc⟩

theorem initCell_old (p : Spec.Argon2.Params) (h0 : List Byte) {l k : Nat}
    (h₀ : k ≠ l * p.laneLen) (h₁ : k ≠ l * p.laneLen + 1) :
    initCell p h0 (l + 1) k = initCell p h0 l k := by
  unfold initCell
  obtain hdm := Nat.div_add_mod k p.laneLen
  by_cases hq : k / p.laneLen = l
  · rw [hq, Nat.mul_comm] at hdm
    rw [ite_eq_right (by omega_arith), ite_eq_right (by omega_arith)]
  · by_cases hc : k / p.laneLen < l ∧ k % p.laneLen < 2
    · rw [ite_eq_left (by omega_arith), ite_eq_left hc]
    · rw [ite_eq_right (by omega_arith), ite_eq_right hc]

/-! ## A lane's first blocks -/

/-- A store to the locals at `d` keeps their first `n ≤ d` bytes. -/
theorem loc_bytes_store {s₀ : State} (hp : DPre s₀) {m : Mem} {d n : Nat} (hn : n ≤ d) (hd : d + 4 ≤ 144)
    (v : BitVec 32) :
    bytesAt (m.writeW (addr (E s₀) d) v) ((E s₀).setWidth 64) n = bytesAt m ((E s₀).setWidth 64) n := by
  have := E_hi hp
  refine bytes_keep
    ((Frame.refl [⟨addr (E s₀) d, 4⟩] m).writeW (List.mem_singleton_self _) v (Region.contains_self _ _))
    (fun r hr => ?_) (by omega_arith)
  simp only [List.mem_singleton] at hr; subst hr
  exact disj32 (.inl (by rw [add_nat (by omega_arith)]; omega_arith)) (by omega_arith) (by rw [add_nat (by omega_arith)]; omega_arith)

/-- The 72 bytes of H′'s input: H₀, then two words. -/
theorem bytes72 (m : Mem) (p : Addr) :
    bytesAt m p 72 = bytesAt m p 64 ++ Spec.Blake2.wordBytes (m.readW (p + BitVec.ofNat 64 64) 32) ++
      Spec.Blake2.wordBytes (m.readW (p + BitVec.ofNat 64 68) 32) := by
  rw [show (72 : Nat) = 64 + (4 + (4 + 0)) from rfl, Proof.Blake2.bytesAt_add, bytes_word, bytes_word,
    BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  simp [bytesAt]

section
variable {s₀ : State} (hp : DPre s₀)
include hp

omit hp in
/-- The call's frame lies in the body's regions. -/
theorem call_sub {O : Region} (hO : Region.Sub O (memR s₀) ∨ Region.Sub O (outR s₀)) :
    ∀ r ∈ [O, scrR s₀, callR s₀], ∃ r' ∈ [memR s₀, scrR s₀, outR s₀, callR s₀], Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rcases hO with h | h
    · exact ⟨_, by simp, h⟩
    · exact ⟨_, by simp, h⟩
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, fun _ h => h⟩

/-- The first 64 bytes of the locals are outside a call's frame. -/
theorem h0_call {O : Region} (hO : Region.Sub O (memR s₀) ∨ Region.Sub O (outR s₀)) :
    ∀ r ∈ [O, scrR s₀, callR s₀], Region.Disjoint ⟨(E s₀).setWidth 64, 64⟩ r := by
  obtain sub : Region.Sub ⟨(E s₀).setWidth 64, 64⟩ (locR s₀) := Region.sub_prefix (by decide)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rcases hO with h | h
    · exact ((loc_disj' hp (R := memR s₀) (by simp)).sub_left sub).sub_right h
    · exact ((loc_disj' hp (R := outR s₀) (by simp)).sub_left sub).sub_right h
  · exact (loc_disj' hp (R := scrR s₀) (by simp)).sub_left sub
  · exact (loc_call hp).sub_left sub

/-- A cell of the memory matrix is outside `scratch`, `out`'s and the stack below the locals. -/
theorem cell_disj {k : Nat} (hk : k < blocksN s₀) :
    ∀ r ∈ [scrR s₀, callR s₀], Region.Disjoint ⟨matrixCell (memB s₀) k, 1024⟩ r := by
  obtain sub : Region.Sub ⟨matrixCell (memB s₀) k, 1024⟩ (memR s₀) := matrixCell_sub _ _ _ hk
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hp.mem_scr.sub_left sub
  · exact (call_disj hp (R := memR s₀) (by simp)).symm.sub_left sub

theorem cell_addr {k : Nat} (hk : k < blocksN s₀) :
    (memP s₀ + BitVec.ofNat 32 (k * 1024)).setWidth 64 = matrixCell (memB s₀) k := by
  have := hp.mem_fits
  have : k * 1024 + 1024 ≤ blocksN s₀ * 1024 := by omega_arith
  exact HPrime.setWidth_add (by omega_arith)

omit hp in
theorem cell_in_mem {k : Nat} (hk : k < blocksN s₀) :
    Region.Sub ⟨matrixCell (memB s₀) k, 1024⟩ (memR s₀) := matrixCell_sub _ _ _ hk

/-- Cells other than `k` are outside its region. -/
theorem cell_other {j k : Nat} (hj : j < blocksN s₀) (hk : k < blocksN s₀) (ne : j ≠ k) :
    Region.Disjoint ⟨matrixCell (memB s₀) j, 1024⟩ ⟨matrixCell (memB s₀) k, 1024⟩ :=
  matrixCell_disjoint _ _ _ _ (by have := hp.blocks_lt; omega_arith) hj hk ne

/-- Block `c < 2` of lane `l`: H′ of H₀, `c` and `l`. -/
theorem initBlock_ok {s : State} (h : Inv s₀ s) (pr : Prm s₀ s) {h0 : List Byte}
    (b0 : bytesAt s.mem ((E s₀).setWidth 64) 64 = h0) {l c : Nat} (hl : l < lanesN s₀) (hc : c < 2)
    (esi : s.gpr .esi = BitVec.ofNat 32 l)
    (edi : s.gpr .edi = memP s₀ + BitVec.ofNat 32 ((l * (prm s₀).laneLen + c) * 1024)) :
    WP isa (Impl.Argon2.X86.Derive.initBlock c) s fun t => Inv s₀ t ∧ Prm s₀ t ∧
      bytesAt t.mem ((E s₀).setWidth 64) 64 = h0 ∧ t.gpr .esi = s.gpr .esi ∧ t.gpr .edi = s.gpr .edi ∧
      blockAt t.mem (matrixCell (memB s₀) (l * (prm s₀).laneLen + c)) = parseBlock (initialBytes h0 l c) ∧
      ∀ k < blocksN s₀, k ≠ l * (prm s₀).laneLen + c →
        blockAt t.mem (matrixCell (memB s₀) k) = blockAt s.mem (matrixCell (memB s₀) k) := by
  obtain hE := E_hi hp
  have hs := hp.scr_fits
  have hm := hp.mem_fits
  have hlt := hp.lanes_lt
  obtain L2 : 2 ≤ (prm s₀).laneLen := by rw [hp.laneLen_eq]; have := hp.segLen_two; omega_arith
  obtain hcell : l * (prm s₀).laneLen + c < blocksN s₀ := by
    rw [hp.blocks_eq]
    have := Nat.mul_le_mul_right (prm s₀).laneLen (show l + 1 ≤ lanesN s₀ by omega_arith)
    rw [Nat.succ_mul] at this
    omega_arith
  unfold Impl.Argon2.X86.Derive.initBlock Impl.Argon2.X86.Derive.hPrimeCall
  refine WP.seq (wp_movi fun s₁ u₁ => ?_)
  obtain i₁ := h.upd u₁ (by decide) (by decide)
  refine wp_stloc hp i₁ (d := 64) (by decide) fun s₂ i₂ v₂ o₂ g₂ m₂ => ?_
  refine wp_stloc hp i₂ (d := 68) (by decide) fun s₃ i₃ v₃ o₃ g₃ m₃ => ?_
  refine wp_movi fun s₄ u₄ => wp_movi fun s₅ u₅ => wp_ldarg hp ((i₃.upd u₄ (by decide) (by decide)).upd u₅
    (by decide) (by decide)) (i := 15) (by decide) fun s₆ u₆ => WP.block_nil ?_
  obtain i₆ := ((i₃.upd u₄ (by decide) (by decide)).upd u₅ (by decide) (by decide)).upd u₆ (by decide) (by decide)
  obtain m₆ : s₆.mem = s₃.mem := by rw [u₆.mem, u₅.mem, u₄.mem]
  obtain g₆ : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → s₆.gpr r = s.gpr r := fun r a b d => by
    rw [u₆.other _ d, u₅.other _ b, u₄.other _ a, g₃, g₂, u₁.other _ a]
  have ebp₆ : s₆.gpr .ebp = E s₀ := i₆.ebp
  obtain eax₆ : (s₆.gpr .eax).toNat = 72 := by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr]; rfl
  obtain ecx₆ : (s₆.gpr .ecx).toNat = 1024 := by rw [u₆.other _ (by decide), u₅.gpr]; rfl
  obtain edi₆ : s₆.gpr .edi = s.gpr .edi := g₆ _ (by decide) (by decide) (by decide)
  obtain O : (s₆.gpr .edi).setWidth 64 = matrixCell (memB s₀) (l * (prm s₀).laneLen + c) := by
    rw [edi₆, edi, cell_addr hp hcell]
  obtain sO : Region.Sub ⟨(s₆.gpr .edi).setWidth 64, (s₆.gpr .ecx).toNat⟩ (memR s₀) := by
    rw [O, ecx₆]; exact cell_in_mem hcell
  obtain hcell' : (l * (prm s₀).laneLen + c) * 1024 + 1024 ≤ blocksN s₀ * 1024 := by omega_arith
  refine hcall_ok hp i₆ (r := .ebp) (by decide) u₆.gpr
    ⟨locR s₀, by simp, 0, by rw [ebp₆]; simp, by rw [eax₆]; show 0 + 72 ≤ 144; omega_arith⟩ (by rw [ebp₆, eax₆]; omega_arith)
    ⟨memR s₀, by simp, (l * (prm s₀).laneLen + c) * 1024, by rw [O]; rfl, by rw [ecx₆]; exact hcell'⟩
    (by rw [edi₆, edi, ecx₆, add_nat (by omega_arith)]; omega_arith) (by rw [ecx₆]; decide)
    fun t it cs fr post => ⟨it, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- The parameters.
    exact Prm.of_lw pr fun d hd => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      obtain hd' : 72 ≤ d ∧ d + 4 ≤ 144 := by rcases hd with rfl | rfl | rfl | rfl <;> decide
      rw [lw_keep hp fr (call_sub (.inl sO)) hd'.2, lw_mem m₆, o₃ d (by omega_arith) (by omega_arith),
        o₂ d (by omega_arith) (by omega_arith), lw_mem u₁.mem]
  · rw [bytes_keep fr (h0_call hp (.inl sO)) (by omega_arith), m₆, m₃,
      loc_bytes_store hp (by decide) (by decide), m₂, loc_bytes_store hp (by decide) (by decide), u₁.mem, b0]
  · rw [cs .esi (by decide), g₆ _ (by decide) (by decide) (by decide)]
  · rw [cs .edi (by decide), edi₆]
  · refine Proof.Argon2.blockAt_of_initialBytes _ _ _ _ _ ?_
    rw [← O, ← ecx₆, post, ecx₆, ebp₆, eax₆, bytes72, m₆]
    obtain w64 : s₃.mem.readW ((E s₀).setWidth 64 + BitVec.ofNat 64 64) 32 = BitVec.ofNat 32 c := by
      rw [← addr_eq (by omega_arith)]
      show lw s₀ s₃ 64 = _
      rw [o₃ 64 (by decide) (by decide), v₂, u₁.gpr]
    obtain w68 : s₃.mem.readW ((E s₀).setWidth 64 + BitVec.ofNat 64 68) 32 = BitVec.ofNat 32 l := by
      rw [← addr_eq (by omega_arith)]
      show lw s₀ s₃ 68 = _
      rw [v₃, g₂, u₁.other _ (by decide), esi]
    rw [w64, w68, m₃, loc_bytes_store hp (by decide) (by decide), m₂, loc_bytes_store hp (by decide) (by decide),
      u₁.mem, b0]
    rfl
  · intro k hk ne
    obtain fs : Frame [⟨addr (E s₀) 64, 4⟩, ⟨addr (E s₀) 68, 4⟩] s.mem s₃.mem := by
      rw [m₃, m₂, u₁.mem]
      exact ((Frame.refl _ _).writeW (w := 32) List.mem_cons_self _ (Region.contains_self _ _)).writeW (w := 32)
        (List.mem_cons_of_mem _ List.mem_cons_self) _ (Region.contains_self _ _)
    rw [blockAt_keep fr (fun r hr => ?_), m₆]
    · -- The stores to the locals.
      refine blockAt_keep fs fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ((loc_disj hp (d := 64) (by decide) (memR s₀) (by simp)).symm.sub_left (cell_in_mem hk))
      · exact ((loc_disj hp (d := 68) (by decide) (memR s₀) (by simp)).symm.sub_left (cell_in_mem hk))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [O, ecx₆]; exact cell_other hp hk hcell ne
      · exact cell_disj hp hk _ (by simp)
      · exact cell_disj hp hk _ (by simp)

end

/-- The state after the first two blocks of `l` lanes. -/
structure LI (s₀ : State) (h0 : List Byte) (l : Nat) (s : State) : Prop where
  inv : Inv s₀ s
  pr : Prm s₀ s
  b0 : bytesAt s.mem ((E s₀).setWidth 64) 64 = h0
  esi : s.gpr .esi = BitVec.ofNat 32 l
  edi : s.gpr .edi = memP s₀ + BitVec.ofNat 32 (l * (prm s₀).laneLen * 1024)
  cells : ∀ k < blocksN s₀, blockAt s.mem (matrixCell (memB s₀) k) = initCell (prm s₀) h0 l k

theorem Prm.of_mem {s₀ s t : State} (pr : Prm s₀ s) (h : t.mem = s.mem) : Prm s₀ t :=
  Prm.of_lw pr fun d _ => lw_mem h d

theorem edi_next (x : BitVec 32) (a b : Nat) :
    x + BitVec.ofNat 32 a + 1024 + BitVec.ofNat 32 b - 1024 = x + BitVec.ofNat 32 (a + b) := by
  rw [BitVec.add_assoc (x + _) 1024, BitVec.add_comm 1024 (BitVec.ofNat 32 b), ← BitVec.add_assoc,
    BitVec.add_sub_cancel, BitVec.add_assoc, BitVec.ofNat_add_ofNat]

section
variable {s₀ : State} (hp : DPre s₀)
include hp

theorem lane_ok {h0 : List Byte} {l : Nat} {s : State} (hl : l < lanesN s₀) (h : LI s₀ h0 l s) :
    WP isa Impl.Argon2.X86.Derive.initLane s fun t =>
      LI s₀ h0 (l + 1) t ∧ t.cf = some (decide (l + 1 < lanesN s₀)) := by
  obtain L2 : 2 ≤ (prm s₀).laneLen := by rw [hp.laneLen_eq]; have := hp.segLen_two; omega_arith
  have hlt := hp.lanes_lt
  unfold Impl.Argon2.X86.Derive.initLane
  refine WP.seq ((initBlock_ok hp h.inv h.pr h.b0 hl (c := 0) (by decide) h.esi
    (by rw [h.edi, Nat.add_zero])).mono fun s₁ ⟨i₁, p₁, b₁, e₁, d₁, w₁, o₁⟩ => ?_)
  refine WP.seq (wp_addi fun s₂ u₂ => WP.block_nil ?_)
  obtain i₂ := i₁.upd u₂ (by decide) (by decide)
  refine WP.seq ((initBlock_ok hp i₂ (p₁.of_mem u₂.mem) (h0 := h0) (by rw [u₂.mem]; exact b₁) hl (c := 1) (by decide)
    (by rw [u₂.other _ (by decide), e₁, h.esi]) (by rw [u₂.gpr, d₁, h.edi, show (1024 : BitVec 32) = BitVec.ofNat 32 1024 from rfl, BitVec.add_assoc,
      BitVec.ofNat_add_ofNat, Nat.succ_mul])).mono fun s₃ ⟨i₃, p₃, b₃, e₃, d₃, w₃, o₃⟩ => ?_)
  simp only [Impl.Argon2.X86.Derive.nextLane, Impl.Argon2.X86.Derive.fr]
  refine wp_ldloc hp i₃ (d := Impl.Argon2.X86.Derive.strideOff) (by decide) fun s₄ u₄ =>
    wp_add fun s₅ u₅ _ => wp_subi fun s₆ u₆ _ _ => wp_addi fun s₇ u₇ => ?_
  obtain i₇ := (((i₃.upd u₄ (by decide) (by decide)).upd u₅ (by decide) (by decide)).upd u₆ (by decide)
    (by decide)).upd u₇ (by decide) (by decide)
  obtain m₇ : s₇.mem = s₃.mem := by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem]
  obtain esi₇ : s₇.gpr .esi = BitVec.ofNat 32 (l + 1) := by
    rw [u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), e₃,
      u₂.other _ (by decide), e₁, h.esi, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
      BitVec.ofNat_add_ofNat]
  refine wp_cmpm i₇.ebp (i₇.arg_in hp (i := 7) (by decide)) fun t f c _ => WP.block_nil ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · exact i₇.step (by rw [f.gpr]) (by rw [f.gpr]) f.rd f.wr (by rw [f.mem]; exact Frame.refl _ _)
  · exact p₃.of_mem (by rw [f.mem, m₇])
  · rw [f.mem, m₇, b₃]
  · rw [f.gpr, esi₇]
  · rw [f.gpr, u₇.other _ (by decide), u₆.gpr, u₅.gpr, u₄.gpr, u₄.other _ (by decide), d₃, u₂.gpr, d₁, h.edi,
      p₃.stride, edi_next, Nat.succ_mul, Nat.add_mul]
  · intro k hk
    rw [f.mem, m₇]
    by_cases k1 : k = l * (prm s₀).laneLen + 1
    · rw [k1, w₃]; exact (initCell_new _ _ L2 (by decide)).symm
    rw [o₃ k hk k1]
    by_cases k0 : k = l * (prm s₀).laneLen
    · rw [u₂.mem, k0, show l * (prm s₀).laneLen = l * (prm s₀).laneLen + 0 from rfl, w₁]
      exact (initCell_new _ _ L2 (by decide)).symm
    rw [u₂.mem, o₁ k hk (by omega_arith), h.cells k hk, initCell_old _ _ k0 k1]
  · rw [c, esi₇, i₇.arg hp (by decide), Wp.toNat_ofNat_lt (by omega_arith)]; rfl

/-- `clear`, from the body with H₀ in the locals. -/
theorem clearW_ok {s : State} (h : Inv s₀ s) (pr : Prm s₀ s) {h0 : List Byte}
    (b0 : bytesAt s.mem ((E s₀).setWidth 64) 64 = h0) :
    WP isa Impl.Argon2.X86.Derive.clear s fun t => Inv s₀ t ∧ Prm s₀ t ∧
      bytesAt t.mem ((E s₀).setWidth 64) 64 = h0 ∧ ∀ i < blocksN s₀ * 1024,
        t.mem ((memP s₀).setWidth 64 + BitVec.ofNat 64 i) = 0 := by
  refine (clear_ok hp h).mono fun s₁ ⟨i₁, f₁, z₁⟩ => ⟨i₁, ?_, ?_, z₁⟩
  · have fsub : ∀ r ∈ [memR s₀], ∃ r' ∈ [memR s₀, scrR s₀, outR s₀, callR s₀], Region.Sub r r' :=
      fun r hr => ⟨r, by simp only [List.mem_singleton] at hr; subst hr; simp, fun _ h => h⟩
    exact Prm.of_lw pr fun d hd => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      exact lw_keep hp f₁ fsub (by rcases hd with rfl | rfl | rfl | rfl <;> decide)
  · rw [bytes_keep f₁ (fun r hr => ?_) (by omega_arith), b0]
    simp only [List.mem_singleton] at hr; subst hr
    exact (loc_disj' hp (R := memR s₀) (by simp)).sub_left (Region.sub_prefix (by decide))

/-- The first lane's first block, after `clear`. -/
theorem laneStart_ok {s : State} {h0 : List Byte} (h : Inv s₀ s ∧ Prm s₀ s ∧
      bytesAt s.mem ((E s₀).setWidth 64) 64 = h0 ∧ ∀ i < blocksN s₀ * 1024,
        s.mem ((memP s₀).setWidth 64 + BitVec.ofNat 64 i) = 0) :
    WP isa (.block [.mov .edi (Impl.Argon2.X86.Derive.fr (Impl.Argon2.X86.Derive.argOff 13)), .mov .esi (.imm 0)]) s (LI s₀ h0 0) := by
  obtain ⟨i₁, p₁, b₁, z₁⟩ := h
  refine wp_ldarg hp i₁ (i := 13) (by decide) fun s₂ u₂ => wp_movi fun s₃ u₃ => WP.block_nil ?_
  obtain i₃ := (i₁.upd u₂ (by decide) (by decide)).upd u₃ (by decide) (by decide)
  obtain m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem]
  refine ⟨i₃, p₁.of_mem m₃, by rw [m₃]; exact b₁, u₃.gpr, ?_, fun k hk => ?_⟩
  · rw [u₃.other _ (by decide), u₂.gpr]; simp
  · rw [initCell_zero, m₃]
    refine blockAt_zero fun i hi => ?_
    rw [matrixCell, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    exact z₁ _ (by omega_arith)

theorem memoryInit_ok {s : State} (h : Inv s₀ s) (pr : Prm s₀ s) {h0 : List Byte}
    (b0 : bytesAt s.mem ((E s₀).setWidth 64) 64 = h0) :
    WP isa Impl.Argon2.X86.Derive.memoryInit s fun t => Inv s₀ t ∧ Prm s₀ t ∧
      Represents t.mem (memB s₀) (prm s₀).blocks (Spec.Argon2.initMemory (prm s₀) h0).memory := by
  have hlt := hp.lanes_lt
  have hl1 := hp.lanes_pos
  have hb := hp.blocks_lt
  unfold Impl.Argon2.X86.Derive.memoryInit
  refine WP.seq ((clearW_ok hp h pr b0).mono fun s₁ h₁ => WP.seq ((laneStart_ok hp h₁).mono fun s₃ start => ?_))
  refine WP.loop (M := isa) (fun n t => ∃ l, n = lanesN s₀ - l ∧ l < lanesN s₀ ∧ LI s₀ h0 l t) ?_
    (lanesN s₀) s₃ ⟨0, by omega_arith, by omega_arith, start⟩
  rintro n t ⟨l, rfl, hl, ht⟩
  refine (lane_ok hp hl ht).mono fun u ⟨hu, cu⟩ => ?_
  by_cases done : l + 1 < lanesN s₀
  · refine .inr ⟨by simp only [eval, cu, done, decide_true], lanesN s₀ - (l + 1), by omega_arith, l + 1, rfl, done, hu⟩
  · refine .inl ⟨by simp only [eval, cu, done, decide_false], hu.inv, hu.pr, ?_⟩
    obtain hl' : l + 1 = lanesN s₀ := by omega_arith
    refine ⟨Proof.Argon2.initMemory_size _ _, fun k hk => ?_⟩
    obtain hk' : k < blocksN s₀ := by rw [hp.blocks]; exact hk
    rw [hu.cells k hk', Array.getElem?_eq_getElem (by rw [Proof.Argon2.initMemory_size]; exact hk),
      Option.getD_some, Proof.Argon2.initMemory_cell _ _ _ hk, initCell, hl']
    have : k / (prm s₀).laneLen < lanesN s₀ := by
      rw [hp.blocks_eq] at hk'
      exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hk')
    by_cases c2 : k % (prm s₀).laneLen < 2
    · rw [ite_eq_left ⟨this, c2⟩, ite_eq_left c2]
    · rw [ite_eq_right (fun h => c2 h.2), ite_eq_right c2]

end

end VG.Proof.Argon2.X86.Derive
