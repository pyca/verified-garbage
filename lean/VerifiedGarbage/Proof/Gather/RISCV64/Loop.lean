module

public import VerifiedGarbage.Impl.Gather.RISCV64
public import VerifiedGarbage.Proof.Framework.RISCV64.Steps
public import VerifiedGarbage.Proof.Framework.RISCV64.Inline
public import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Spec.Gcm.OutOfPlace
import VerifiedGarbage.Proof.Framework.RISCV64.Loops
import VerifiedGarbage.Proof.Framework.RISCV64.Bytes
import VerifiedGarbage.Proof.Framework.RISCV64.Keep
import VerifiedGarbage.Proof.Gcm.SealGather
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit

/-!
# Gathering a list of slices, RISC-V: the loop

`gather` copies the `cnt` slices that the descriptors at `a4` list, one after
the other, to `a6` (`gather_wp`): with `i` of them copied, `a4` is at
descriptor `i`, `a5` holds `cnt - i`, `a6` is `gatheredLen` of the first `i`
past `dst`, and the memory is the one on entry with their concatenation
(`gathered`) written at `dst`. The descriptors and the slices are apart from
`dst`, so they are what they were on entry. As on PPC64LE
(`Proof/Gather/PPC64LE/Loop.lean`), with each slice copied a byte at a time
(`copyLoop_adv`).
-/

@[expose] public section

namespace VG.Proof.Gather.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Gather.RISCV64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (gathered gatheredLen)

/-- The registers the gathering writes. -/
abbrev gatherRegs : List Reg := [.t0, .t1, .t2, .t3, .t4, .a4, .a5, .a6]

/-- What the gathering keeps: the other registers, the stack pointer and the
permissions. -/
structure GKeeps (s t : State) : Prop where
  gpr : ∀ r, r ∉ gatherRegs → t.gpr r = s.gpr r
  sp : t.sp = s.sp
  rd : t.rd = s.rd
  wr : t.wr = s.wr

theorem GKeeps.refl (s : State) : GKeeps s s := ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

theorem GKeeps.trans {s t u : State} (h₁ : GKeeps s t) (h₂ : GKeeps t u) : GKeeps s u :=
  ⟨fun r hr => (h₂.gpr r hr).trans (h₁.gpr r hr), h₂.sp.trans h₁.sp, h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr⟩

theorem gkeeps_of_upd {s t : State} {d : Reg} {v : BitVec 64} (u : Upd s t d v)
    (hd : d ∈ gatherRegs := by decide) : GKeeps s t :=
  ⟨fun r hr => u.other r fun e => hr (e ▸ hd), u.sp, u.rd, u.wr⟩

section
variable (m : Mem) (Src : Addr)

/-- Slice `i`: its address and its length. -/
abbrev sb (i : Nat) : Addr := m.readW (Src + BitVec.ofNat 64 (16 * i)) 64
abbrev sl (i : Nat) : Nat := (m.readW (Src + BitVec.ofNat 64 (16 * i) + BitVec.ofNat 64 8) 64).toNat

end

theorem desc_off (i : Nat) : i * (2 * (64 / 8)) = 16 * i := by omega

theorem gl_succ (m : Mem) (Src : Addr) (i : Nat) :
    gatheredLen 64 m Src (i + 1) = gatheredLen 64 m Src i + sl m Src i := by
  rw [Proof.Gcm.gatheredLen_succ, desc_off]

theorem pt_succ (m : Mem) (Src : Addr) (i : Nat) :
    gathered 64 m Src (i + 1) = gathered 64 m Src i ++ bytesAt m (sb m Src i) (sl m Src i) := by
  rw [Proof.Gcm.gathered_succ, desc_off, BitVec.setWidth_eq]

theorem gl_mono (m : Mem) (Src : Addr) {i j : Nat} (h : i ≤ j) :
    gatheredLen 64 m Src i ≤ gatheredLen 64 m Src j := by
  induction j with
  | zero => rw [Nat.le_zero.mp h]
  | succ j ih =>
    rcases Nat.eq_or_lt_of_le h with rfl | h
    · exact Nat.le_refl _
    · rw [gl_succ]; exact Nat.le_trans (ih (by omega)) (Nat.le_add_right _ _)

/-- Slice `i` is listed. -/
theorem slice_mem (m : Mem) (Src : Addr) {i cnt : Nat} (hi : i < cnt) :
    (⟨sb m Src i, sl m Src i⟩ : Region) ∈ Sig.listed 64 m .u8 Src cnt := by
  simp only [Sig.listed, List.mem_map, List.mem_range]
  refine ⟨i, hi, ?_⟩
  simp only [desc_off, BitVec.setWidth_eq, Elem.size, Nat.mul_one]

/-! ## Regions -/

theorem covers_off {p : Addr} {k d n : Nat} {rs : List Region} (h : Covers [⟨p, k⟩] rs) (hd : d + n ≤ k)
    (hk : k < 2 ^ 64) : Covers [⟨p + BitVec.ofNat 64 d, n⟩] rs := by
  intro a m ⟨r, hr, hc⟩
  simp only [List.mem_singleton] at hr; subst hr
  refine h a m ⟨_, List.mem_singleton_self _, ?_⟩
  simp only [Region.Contains] at hc ⊢
  have e : a - p = (a - (p + BitVec.ofNat 64 d)) + BitVec.ofNat 64 d := by
    rw [Offset.sub_add_eq]; exact (BitVec.sub_add_cancel _ _).symm
  rw [e, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := d) (by omega_arith),
    Nat.mod_eq_of_lt (by omega_arith)]
  omega_arith

theorem in_off {p : Addr} {k d n : Nat} {rs : List Region} (h : Covers [⟨p, k⟩] rs) (hd : d + n ≤ k)
    (hk : k < 2 ^ 64) : InRegions rs (p + BitVec.ofNat 64 d) n :=
  covers_off h hd hk _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩

/-- Bytes outside a frame are unchanged. -/
theorem bytesAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨p, n⟩ : Region).Disjoint r) (hn : n ≤ 2 ^ 64) : bytesAt m' p n = bytesAt m p n := by
  simp only [bytesAt]
  apply List.map_congr_left
  intro i hi
  exact hf.bytes (R := ⟨p, n⟩) hd hn (List.mem_range.mp hi)

/-- A copy, byte by byte, as the bytes written. -/
theorem mem_of_copy {m m' : Mem} {S D : Addr} {n : Nat}
    (hc : ∀ i < n, m' (D + BitVec.ofNat 64 i) = m (S + BitVec.ofNat 64 i)) (hf : Frame [⟨D, n⟩] m m') :
    m' = writeBytes m D (bytesAt m S n) := by
  funext x
  by_cases h : (x - D).toNat < n
  · have e : x = D + BitVec.ofNat 64 (x - D).toNat := by
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
    have := hc _ h
    rw [← e] at this
    rw [this]
    simp only [writeBytes, Proof.Cmac.bytesAt_length, h, ↓reduceIte]
    simp only [bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range h, Option.map_some,
      Option.getD_some]
  · simp only [writeBytes, Proof.Cmac.bytesAt_length, h, ↓reduceIte]
    exact hf x fun r hr hc' => by
      simp only [List.mem_singleton] at hr; subst hr
      simp only [Region.Contains] at hc'; omega

/-! ## The loop -/

/-- What the gathering needs: `cnt` descriptors at `Src`, listing slices of
`L` bytes in all, to copy to `Dst`, apart from them. -/
structure GatherPre (t : State) (Src Dst : Addr) (cnt L : Nat) : Prop where
  a4 : t.gpr .a4 = Src
  a5 : t.gpr .a5 = BitVec.ofNat 64 cnt
  a6 : t.gpr .a6 = Dst
  hcnt : cnt < 2 ^ 64
  dw : Src.toNat + cnt * 16 ≤ 2 ^ 64
  lt : L < 2 ^ 64
  len : gatheredLen 64 t.mem Src cnt = L
  dsr : Covers [⟨Src, cnt * 16⟩] (t.rd ++ t.wr)
  lsr : ∀ r ∈ Sig.listed 64 t.mem .u8 Src cnt, Covers [r] (t.rd ++ t.wr)
  dw' : Covers [⟨Dst, L⟩] t.wr
  dsd : (⟨Src, cnt * 16⟩ : Region).Disjoint ⟨Dst, L⟩
  lsd : ∀ r ∈ Sig.listed 64 t.mem .u8 Src cnt, r.Disjoint ⟨Dst, L⟩

/-- The loop's invariant: the first `i` slices copied. -/
structure GInv (t u : State) (Src Dst : Addr) (cnt i : Nat) : Prop where
  a4 : u.gpr .a4 = Src + BitVec.ofNat 64 (16 * i)
  a5 : u.gpr .a5 = BitVec.ofNat 64 (cnt - i)
  a6 : u.gpr .a6 = Dst + BitVec.ofNat 64 (gatheredLen 64 t.mem Src i)
  mem : u.mem = writeBytes t.mem Dst (gathered 64 t.mem Src i)
  keep : GKeeps t u

/-- After `next`: descriptor `i` loaded. -/
structure NInv (t u : State) (Src Dst : Addr) (cnt i : Nat) : Prop where
  a4 : u.gpr .a4 = Src + BitVec.ofNat 64 (16 * (i + 1))
  a5 : u.gpr .a5 = BitVec.ofNat 64 (cnt - i)
  a6 : u.gpr .a6 = Dst + BitVec.ofNat 64 (gatheredLen 64 t.mem Src i)
  t0 : u.gpr .t0 = sb t.mem Src i
  t1 : u.gpr .t1 = BitVec.ofNat 64 (sl t.mem Src i)
  mem : u.mem = writeBytes t.mem Dst (gathered 64 t.mem Src i)
  keep : GKeeps t u

theorem GInv.init {t : State} {Src Dst : Addr} {cnt L : Nat} (h : GatherPre t Src Dst cnt L) :
    GInv t t Src Dst cnt 0 :=
  ⟨by rw [h.a4]; exact (BitVec.add_zero _).symm, by rw [h.a5, Nat.sub_zero],
    by rw [h.a6]; simp [gatheredLen, Sig.listed], by simp [gathered, Sig.listed, writeBytes_nil],
    GKeeps.refl t⟩

section
variable {t u : State} {Src Dst : Addr} {cnt L i : Nat} (h : GatherPre t Src Dst cnt L)
include h

omit h in
/-- What the loop has written is within `dst`. -/
theorem frame_of {xs : List Byte} (hm : u.mem = writeBytes t.mem Dst xs) (hx : xs.length ≤ L) :
    Frame [⟨Dst, L⟩] t.mem u.mem := by
  rw [hm]
  refine writeBytes_frame t.mem Dst _ ?_
  simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]
  omega

theorem gl_le (hi : i ≤ cnt) : gatheredLen 64 t.mem Src i ≤ L := h.len ▸ gl_mono t.mem Src hi

theorem len_le (hi : i ≤ cnt) : (gathered 64 t.mem Src i).length ≤ L :=
  (Proof.Gcm.length_gathered _ _ _ _) ▸ gl_le h hi

/-- The descriptors are what they were. -/
theorem desc_of (hf : Frame [⟨Dst, L⟩] t.mem u.mem) (d : Nat) (hd : d + 8 ≤ cnt * 16) :
    u.mem.readW (Src + BitVec.ofNat 64 d) 64 = t.mem.readW (Src + BitVec.ofNat 64 d) 64 :=
  hf.readW (r := ⟨Src, cnt * 16⟩) (Offset.contains_base Src hd (by have := h.dw; omega))
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact h.dsd) (by decide)

theorem next_wp (hi : i < cnt) (hu : GInv t u Src Dst cnt i) :
    WP isa (.block next) u (NInv t · Src Dst cnt i) := by
  have hdw := h.dw
  have hfr := frame_of (t := t) hu.mem (len_le h (Nat.le_of_lt hi))
  have hin (d : Nat) (hd : d + 4 ≤ 16) (s : State) (hrd : s.rd = t.rd) (hwr : s.wr = t.wr) :
      InRegions (s.rd ++ s.wr) (Src + BitVec.ofNat 64 (16 * i + d)) 4 := by
    rw [hrd, hwr]
    exact h.dsr _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base Src (by omega) (by omega)⟩
  have ha : ∀ d, u.gpr .a4 + BitVec.ofNat 64 d = Src + BitVec.ofNat 64 (16 * i + d) := fun d => by
    rw [hu.a4, Offset.add_add]
  unfold next
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (Bytes.loadLE64_ok (d := .t0) (tmp := .t3) (hi := .t4) (n := .a4) (off := 0) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [ha]; exact hin 0 (by decide) u hu.keep.rd hu.keep.wr)
    (by rw [ha]; exact hin 4 (by decide) u hu.keep.rd hu.keep.wr))
    fun u₁ ⟨d₁, g₁, m₁, rd₁, wr₁, sp₁⟩ => ?_
  rw [WP.block_append_iff]
  have a4₁ : u₁.gpr .a4 = u.gpr .a4 := g₁ _ (by decide) (by decide) (by decide)
  refine WP.mono (Bytes.loadLE64_ok (d := .t1) (tmp := .t3) (hi := .t4) (n := .a4) (off := 8) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [a4₁, ha]; exact hin 8 (by decide) u₁ (rd₁.trans hu.keep.rd) (wr₁.trans hu.keep.wr))
    (by rw [a4₁, ha]; exact hin 12 (by decide) u₁ (rd₁.trans hu.keep.rd) (wr₁.trans hu.keep.wr)))
    fun u₂ ⟨d₂, g₂, m₂, rd₂, wr₂, sp₂⟩ => ?_
  refine wp_addi (imm := 16) (by decide) fun u₃ v₃ => WP.block_nil ?_
  have k₂ : GKeeps u u₂ :=
    ⟨fun r hr => by
      simp only [gatherRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      rw [g₂ r hr.2.1 hr.2.2.2.1 hr.2.2.2.2.1, g₁ r hr.1 hr.2.2.2.1 hr.2.2.2.2.1],
      sp₂.trans sp₁, rd₂.trans rd₁, wr₂.trans wr₁⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hu.keep.trans (k₂.trans (gkeeps_of_upd v₃))⟩
  · rw [v₃.gpr, g₂ _ (by decide) (by decide) (by decide), a4₁, hu.a4, Offset.add_add, Nat.mul_succ]
  · rw [v₃.other _ (by decide), g₂ _ (by decide) (by decide) (by decide), g₁ _ (by decide) (by decide)
      (by decide), hu.a5]
  · rw [v₃.other _ (by decide), g₂ _ (by decide) (by decide) (by decide), g₁ _ (by decide) (by decide)
      (by decide), hu.a6]
  · rw [v₃.other _ (by decide), g₂ _ (by decide) (by decide) (by decide), d₁, ha, Nat.add_zero,
      desc_of h hfr _ (by omega)]
  · rw [v₃.other _ (by decide), d₂, a4₁, ha, m₁, desc_of h hfr _ (by omega), ← Offset.add_add,
      BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · rw [v₃.mem, m₂, m₁, hu.mem]

theorem rest_wp (hi : i < cnt) (hu : NInv t u Src Dst cnt i) :
    WP isa (.seq copySlice (.block [.addi .a5 .a5 (-1)])) u (GInv t · Src Dst cnt (i + 1)) := by
  have hc := h.hcnt
  have hL := h.lt
  have hgl : gatheredLen 64 t.mem Src (i + 1) ≤ L := gl_le h (by omega)
  have hlen : (gathered 64 t.mem Src i).length = gatheredLen 64 t.mem Src i :=
    Proof.Gcm.length_gathered _ _ _ _
  rw [gl_succ] at hgl
  have hfr := frame_of (t := t) hu.mem (len_le h (Nat.le_of_lt hi))
  have hmem := slice_mem t.mem Src hi
  have hsd : (⟨sb t.mem Src i, sl t.mem Src i⟩ : Region).Disjoint ⟨Dst, L⟩ := h.lsd _ hmem
  have hsub : (⟨Dst + BitVec.ofNat 64 (gatheredLen 64 t.mem Src i), sl t.mem Src i⟩ : Region).Sub ⟨Dst, L⟩ :=
    Offset.sub_base _ hgl
  have hsl : sl t.mem Src i < 2 ^ 64 := BitVec.isLt _
  -- The slice's bytes were what they were on entry.
  have hbytes : bytesAt u.mem (sb t.mem Src i) (sl t.mem Src i) =
      bytesAt t.mem (sb t.mem Src i) (sl t.mem Src i) := by
    refine bytesAt_frame hfr (fun r hr => ?_) (by omega)
    simp only [List.mem_singleton] at hr; subst hr
    exact hsd
  -- After the copy: the slice written at `a6`, which is past it.
  have post : ∀ u₂ : State, u₂.mem = writeBytes u.mem (Dst + BitVec.ofNat 64 (gatheredLen 64 t.mem Src i))
      (bytesAt u.mem (sb t.mem Src i) (sl t.mem Src i)) →
      u₂.gpr .a6 = Dst + BitVec.ofNat 64 (gatheredLen 64 t.mem Src i + sl t.mem Src i) →
      (∀ r, r ∉ [.t0, .t1, .t2, .a6] → u₂.gpr r = u.gpr r) → u₂.sp = u.sp → u₂.rd = u.rd → u₂.wr = u.wr →
      WP isa (.block [.addi .a5 .a5 (-1)]) u₂ (GInv t · Src Dst cnt (i + 1)) := by
    intro u₂ m₂ a6₂ g₂ sp₂ rd₂ wr₂
    refine wp_subi (imm := 1) (by decide) fun u₃ v₃ => WP.block_nil ?_
    have k₂ : GKeeps u u₂ := ⟨fun r hr => g₂ r (by
      simp only [gatherRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr ⊢
      exact ⟨hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.2.2.2.2⟩), sp₂, rd₂, wr₂⟩
    refine ⟨?_, ?_, ?_, ?_, hu.keep.trans (k₂.trans (gkeeps_of_upd v₃))⟩
    · rw [v₃.other _ (by decide), g₂ _ (by decide), hu.a4]
    · rw [v₃.gpr, g₂ _ (by decide), hu.a5, Offset.ofNat_sub_ofNat (by omega), Nat.sub_sub]
    · rw [v₃.other _ (by decide), a6₂, ← gl_succ]
    · rw [v₃.mem, m₂, hbytes, hu.mem, pt_succ, ← hlen,
        writeBytes_append _ _ _ _ (by rw [hlen, Proof.Cmac.bytesAt_length]; omega)]
  unfold copySlice
  refine WP.seq (WP.ite (decide (sl t.mem Src i = 0)) (eval_zero_ofNat u .t1 hsl hu.t1) (fun ht => ?_)
    (fun hf => ?_))
  · have h0 : sl t.mem Src i = 0 := by simpa using ht
    refine WP.block_nil (post u ?_ ?_ (fun _ _ => rfl) rfl rfl rfl)
    · rw [h0]; simp [bytesAt, writeBytes_nil]
    · rw [hu.a6, h0, Nat.add_zero]
  · have h0 : sl t.mem Src i ≠ 0 := by simpa using hf
    have hw : Covers [⟨Dst + BitVec.ofNat 64 (gatheredLen 64 t.mem Src i), sl t.mem Src i⟩] u.wr := by
      rw [hu.keep.wr]; exact covers_off h.dw' hgl hL
    have hr : Covers [⟨sb t.mem Src i, sl t.mem Src i⟩] (u.rd ++ u.wr) := by
      rw [hu.keep.rd, hu.keep.wr]; exact h.lsr _ hmem
    have hsd' := hsd.sub_right hsub
    refine (WP.rdwr (copyLoop_adv (tmp := .t2) (src := .t0) (dst := .a6) (cnt := .t1) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) u (Nat.pos_of_ne_zero h0) hsl hu.t1
      (fun j hj => by rw [hu.t0]; exact in_off hr (by omega) hsl)
      (fun j hj => by rw [hu.a6]; exact in_off hw (by omega) hsl)
      (fun x h₁ h₂ => by
        rw [hu.a6] at h₁; rw [hu.t0] at h₂
        exact hsd' x (by simp only [Region.Contains]; omega) (by simp only [Region.Contains]; omega)))).mono
      fun u₂ ⟨⟨c₂, f₂, k₂, a6₂⟩, rd₂, wr₂, sp₂⟩ => post u₂ ?_ ?_ (fun r hr => k₂.gpr (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr ⊢
        exact ⟨hr.2.2.1, hr.1, hr.2.2.2, hr.2.1⟩)) sp₂ rd₂ wr₂
    · rw [hu.a6, hu.t0] at c₂; rw [hu.a6] at f₂
      exact mem_of_copy c₂ f₂
    · rw [a6₂, hu.a6, Offset.add_add]

end

/-- `gatherLoop`: the `cnt ≥ 1` slices copied to `Dst`. -/
theorem gatherLoop_wp (t : State) {Src Dst : Addr} {cnt L : Nat} (h : GatherPre t Src Dst cnt L)
    (hpos : 1 ≤ cnt) :
    WP isa gatherLoop t fun t' => t'.mem = writeBytes t.mem Dst (gathered 64 t.mem Src cnt) ∧ GKeeps t t' := by
  have hc := h.hcnt
  refine WP.loop (M := isa) (c := .nonzero .a5)
    (fun (w : Nat) (u : State) => ∃ i, w = cnt - i ∧ i < cnt ∧ GInv t u Src Dst cnt i) ?_ (cnt - 0) _
    ⟨0, rfl, hpos, GInv.init h⟩
  rintro w u ⟨i, rfl, hi, hu⟩
  refine WP.seq (WP.mono (next_wp h hi hu) fun u₁ h₁ => WP.mono (rest_wp h hi h₁) fun u₃ h₃ => ?_)
  have ev := eval_nonzero_ofNat u₃ .a5 (k := cnt - (i + 1)) (by omega) h₃.a5
  by_cases he : i + 1 = cnt
  · left
    exact ⟨by rw [ev]; simp [he], by rw [h₃.mem, he], h₃.keep⟩
  · right
    exact ⟨by rw [ev]; simp; omega, cnt - (i + 1), by omega, i + 1, rfl, by omega, h₃⟩

/-- `gather`: the `cnt` slices copied to `Dst`. -/
theorem gather_wp (t : State) {Src Dst : Addr} {cnt L : Nat} (h : GatherPre t Src Dst cnt L) :
    WP isa gather t fun t' => t'.mem = writeBytes t.mem Dst (gathered 64 t.mem Src cnt) ∧ GKeeps t t' := by
  refine WP.ite (decide (cnt = 0)) (eval_zero_ofNat t .a5 h.hcnt h.a5) (fun ht => ?_) (fun hf => ?_)
  · have h0 : cnt = 0 := by simpa using ht
    subst h0
    exact WP.block_nil ⟨by simp [gathered, Sig.listed, writeBytes_nil], GKeeps.refl t⟩
  · have h0 : cnt ≠ 0 := by simpa using hf
    exact gatherLoop_wp t h (by omega)

end VG.Proof.Gather.RISCV64
