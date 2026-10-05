import VerifiedGarbage.Proof.Blake2.X86.Contract
import VerifiedGarbage.Proof.MdStream.X86.Words
import VerifiedGarbage.Proof.Framework.X86.Wp
import VerifiedGarbage.Proof.Framework.X86.Spill
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Impl.Blake2.X86.Stream
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Sha512.Word64

/- Proofs formerly in `VerifiedGarbage.Proof.Blake2.X86.Stream.Common`. -/
section

/-!
# Streaming BLAKE2 on x86 (32-bit): common lemmas

What the proofs of `init`, `update` and `finalize` need of the parameters
(`Ok`) and of the compression function they call (`CalleeOk`: BLAKE2s's or
BLAKE2b's, verified against `compressX86`), the call (`call_ok`), and the loop
copying bytes into the buffer (`copyLoop_ok`).
-/

namespace VG.Proof.Blake2.X86.Stream

open VG VG.X86 VG.X86.Wp VG.Spec.Blake2
open VG.Impl.Blake2.X86 (at_)
open VG.Impl.Blake2.X86.Stream
open VG.Proof.Blake2 (compressX86 stateAt_congr compressBlocks_congr)
open VG.WriteBytes (writeBytes writeBytes_snoc writeBytes_frame writeBytes_nil)

variable {w : Nat} {P : VG.Spec.Blake2.Params w}

/-- The word sizes. -/
structure Ok (P : VG.Spec.Blake2.Params w) : Prop where
  /-- A key fits in a block. -/
  max : P.maxBytes ≤ blockBytes w
  w : w = 64 ∨ w = 32

theorem Ok.bb (h : VG.Proof.Blake2.X86.Stream.Ok P) : blockBytes w = 64 ∨ blockBytes w = 128 := by
  rcases h.w with rfl | rfl <;> decide

theorem Ok.N (h : VG.Proof.Blake2.X86.Stream.Ok P) : bufOff w = blockBytes w / 2 := by
  rcases h.w with rfl | rfl <;> decide

theorem Ok.pos (h : VG.Proof.Blake2.X86.Stream.Ok P) : 0 < blockBytes w := by rcases h.bb with h | h <;> omega

theorem Ok.len (h : VG.Proof.Blake2.X86.Stream.Ok P) : bufOff w + blockBytes w ≤ 192 := by
  rcases h.w with rfl | rfl <;> decide

theorem N_eq : Impl.Blake2.X86.Stream.N w = bufOff w := rfl
theorem B_eq : Impl.Blake2.X86.Stream.B w = blockBytes w := rfl

/-- What the calls need of the compression function: its contract, and that
it does not touch `esp` but to call, and calls nothing that uses the stack. -/
structure CalleeOk (P : VG.Spec.Blake2.Params w) (code : Prog isa) : Prop where
  verified : ∀ s, (compressX86 P).pre s →
    ∃ t s', Exec isa code s t s' ∧ abiPreserved s s' ∧ (compressX86 P).post s s'
  nosp : NoSp code
  stack : stackUse code = 0

/-- `CalleeOk` from the compression function's `Verified` proof and two
checks the kernel evaluates (`NoSp.of_all (by lit_decide)`, `by lit_decide`). -/
theorem CalleeOk.of_verified {code : Prog isa} (hv : Verified X86.target code (compressX86 P))
    (hn : NoSp code) (hs : stackUse code = 0) : VG.Proof.Blake2.X86.Stream.CalleeOk P code :=
  ⟨hv.1, hn, hs⟩


/-! ## Instructions that keep the flags -/

section
variable {is : List Instr} {s : State} {Q : State → Prop}

/-- `mov d, [b + o]`, which keeps the flags. -/
theorem wp_ldmF {d b : Reg} {B : BitVec 32} {o : Nat} (hb : s.gpr b = B)
    (hin : InRegions (s.rd ++ s.wr) (addr B o) 4)
    (k : ∀ s', Upd s s' d (s.mem.readW (addr B o) 32) → s'.cf = s.cf → s'.zf = s.zf →
      WP isa (.block is) s' Q) :
    WP isa (.block (.mov d (.mem ⟨b, o⟩) :: is)) s Q :=
  cons (s' := s.setReg d _) (by simp [exec, readSrc_mem hb hin]) (k _ (Upd.setReg _ _ _) rfl rfl)

/-- `mov d, r`, which keeps the flags. -/
theorem wp_movF {d r : Reg}
    (k : ∀ s', Upd s s' d (s.gpr r) → s'.cf = s.cf → s'.zf = s.zf → WP isa (.block is) s' Q) :
    WP isa (.block (.mov d (.reg r) :: is)) s Q :=
  cons rfl (k _ (Upd.setReg _ _ _) rfl rfl)

/-- `mov d, v`, which keeps the flags. -/
theorem wp_moviF {d : Reg} {v : BitVec 32}
    (k : ∀ s', Upd s s' d v → s'.cf = s.cf → s'.zf = s.zf → WP isa (.block is) s' Q) :
    WP isa (.block (.mov d (.imm v) :: is)) s Q :=
  cons rfl (k _ (Upd.setReg _ _ _) rfl rfl)

/-- `add d, v`, and the carry. -/
theorem wp_addiC {d : Reg} {v : BitVec 32}
    (k : ∀ s', Upd s s' d (s.gpr d + v) → s'.cf = some (decide (2 ^ 32 ≤ (s.gpr d).toNat + v.toNat)) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.alu .add d (.imm v) :: is)) s Q :=
  cons rfl (k _ (Upd.flags _ _ _ _ _ _) rfl)

/-- `adc d, 0`, after a carry `c`. -/
theorem wp_adc0 {d : Reg} {c : Bool} (hc : s.cf = some c)
    (k : ∀ s', Upd s s' d (s.gpr d + (BitVec.ofBool c).setWidth 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .adc d (.imm 0) :: is)) s Q := by
  have hx : exec (.alu .adc d (.imm 0)) s = some ((arithFlags s (s.gpr d + 0 + (BitVec.ofBool c).setWidth 32)
      (decide (2 ^ 32 ≤ (s.gpr d).toNat + (0 : BitVec 32).toNat + c.toNat))
      (addOverflow (s.gpr d) 0 (s.gpr d + 0 + (BitVec.ofBool c).setWidth 32))).setReg d
      (s.gpr d + 0 + (BitVec.ofBool c).setWidth 32)) := by
    simp only [exec, execAlu, readSrc, Option.bind_some, hc, Option.map_some]
  refine cons hx (k _ ⟨?_, fun r h => ?_, rfl, rfl, rfl⟩)
  · simp [State.setReg]
  · simp [State.setReg, arithFlags, State.setFlags, h]

/-- `and d, v`, and ZF. -/
theorem wp_andiZ {d : Reg} {v : BitVec 32}
    (k : ∀ s', Upd s s' d (s.gpr d &&& v) → s'.zf = some (s.gpr d &&& v == 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .and d (.imm v) :: is)) s Q :=
  cons rfl (k _ (Upd.flags _ _ _ _ _ _) rfl)

/-- `or d, r`, and ZF. -/
theorem wp_orZ {d r : Reg}
    (k : ∀ s', Upd s s' d (s.gpr d ||| s.gpr r) → s'.zf = some (s.gpr d ||| s.gpr r == 0) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.alu .or d (.reg r) :: is)) s Q :=
  cons rfl (k _ (Upd.flags _ _ _ _ _ _) rfl)

end

/-! ## 64-bit counters as two words -/

theorem lo_ofNat (T : Nat) : (BitVec.ofNat 32 T).toNat = T % 2 ^ 32 := BitVec.toNat_ofNat _ _

/-- The carry of adding `a < 2^32` to the low word of `T`, added to its high
word: the high word of `T + a`. -/
theorem carry_ofNat (T a : Nat) (ha : a < 2 ^ 32) :
    BitVec.ofNat 32 (T / 2 ^ 32) +
        (BitVec.ofBool (decide (2 ^ 32 ≤ (BitVec.ofNat 32 T).toNat + (BitVec.ofNat 32 a).toNat))).setWidth 32 =
      BitVec.ofNat 32 ((T + a) / 2 ^ 32) := by
  apply BitVec.eq_of_toNat_eq
  rw [VG.Proof.Blake2.X86.Stream.lo_ofNat, VG.Proof.Blake2.X86.Stream.lo_ofNat, Nat.mod_eq_of_lt ha]
  by_cases h : 2 ^ 32 ≤ T % 2 ^ 32 + a
  · simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_setWidth, BitVec.toNat_ofBool, h,
      decide_true, Bool.toNat_true]
    omega
  · simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_setWidth, BitVec.toNat_ofBool, h,
      decide_false, Bool.toNat_false]
    omega

/-- The two words of `T < 2^64`, high word first, are `T`. -/
theorem append_ofNat {T : Nat} (h : T < 2 ^ 64) :
    (BitVec.ofNat 32 (T / 2 ^ 32) ++ BitVec.ofNat 32 T).toNat = T := by
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt (BitVec.ofNat 32 T).isLt, Nat.shiftLeft_eq,
    VG.Proof.Blake2.X86.Stream.lo_ofNat, VG.Proof.Blake2.X86.Stream.lo_ofNat, Nat.mod_eq_of_lt (by omega)]
  omega

theorem append_toNat_mod (a b : BitVec 32) : (a ++ b).toNat % 2 ^ 32 = b.toNat := by
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt b.isLt, Nat.shiftLeft_eq]
  have := b.isLt; omega

theorem append_toNat_div (a b : BitVec 32) : (a ++ b).toNat / 2 ^ 32 = a.toNat := by
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt b.isLt, Nat.shiftLeft_eq]
  have := b.isLt; omega

theorem lo_append (a b : BitVec 32) : BitVec.ofNat 32 (a ++ b).toNat = b := by
  apply BitVec.eq_of_toNat_eq; rw [VG.Proof.Blake2.X86.Stream.lo_ofNat, VG.Proof.Blake2.X86.Stream.append_toNat_mod]

theorem hi_append (a b : BitVec 32) : BitVec.ofNat 32 ((a ++ b).toNat / 2 ^ 32) = a := by
  apply BitVec.eq_of_toNat_eq; rw [VG.Proof.Blake2.X86.Stream.lo_ofNat, VG.Proof.Blake2.X86.Stream.append_toNat_div, Nat.mod_eq_of_lt a.isLt]



/-! ## Addresses and bytes -/

/-- `x + c`, zero-extended, where it does not wrap around. -/
theorem sw_add {x : BitVec 32} {c : Nat} (h : x.toNat + c < 2 ^ 32) :
    (x + BitVec.ofNat 32 c).setWidth 64 = x.setWidth 64 + BitVec.ofNat 64 c := by
  have := MdStream.X86.addr_add_ofNat (x := x) (k := c) (d := 0) (by omega)
  simpa [addr] using this

theorem toNat_add_ofNat {x : BitVec 32} {c : Nat} (h : x.toNat + c < 2 ^ 32) :
    (x + BitVec.ofNat 32 c).toNat = x.toNat + c := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := c) (by omega), Nat.mod_eq_of_lt h]

theorem bytesAt_length (m : Mem) (p : Addr) (n : Nat) : (VG.Spec.Blake2.bytesAt m p n).length = n := by simp [VG.Spec.Blake2.bytesAt]

/-- Bytes `[0, r)` from `p` stay, and the bytes `xs` follow them. -/
theorem bytesAt_writeBytes (m : Mem) (p : Addr) (r : Nat) (xs : List Byte) (h : r + xs.length < 2 ^ 64) :
    VG.Spec.Blake2.bytesAt (VG.WriteBytes.writeBytes m (p + BitVec.ofNat 64 r) xs) p (r + xs.length) = VG.Spec.Blake2.bytesAt m p r ++ xs := by
  simp only [VG.Spec.Blake2.bytesAt, List.range_add, List.map_append, List.map_map]
  congr 1
  · apply List.map_congr_left
    intro i hi
    have hi := List.mem_range.mp hi
    exact VG.WriteBytes.writeBytes_before m p xs hi (by omega)
  · apply List.ext_getElem (by simp)
    intro j h₁ h₂
    simp only [List.getElem_map, List.getElem_range, Function.comp, VG.WriteBytes.writeBytes]
    have hj : j < xs.length := by simpa using h₁
    rw [show p + BitVec.ofNat 64 (r + j) - (p + BitVec.ofNat 64 r) = BitVec.ofNat 64 j from
      Offset.add_ofNat_add_sub p r j, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    simp [hj, List.getD_eq_getElem?_getD]

/-! ## The streaming state depends only on its bytes -/

theorem reprR_congr (hP : VG.Proof.Blake2.X86.Stream.Ok P) {h0 : VG.Spec.Blake2.HashValue w} {mem mem' : Mem} {p : Addr} {d : List Byte} {r : Nat}
    (hm : ∀ i < bufOff w + blockBytes w, mem' (p + BitVec.ofNat 64 i) = mem (p + BitVec.ofNat 64 i))
    (h : Proof.Blake2.ReprR P h0 mem p d r) : Proof.Blake2.ReprR P h0 mem' p d r := by
  have hN := hP.len
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨h1, h2, h3, by rw [← h4]; exact stateAt_congr fun i hi => hm i (by omega), ?_⟩
  rw [← h5]
  refine Proof.Blake2.bytesAt_congr fun i hi => ?_
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  exact hm _ (by omega)

theorem repr_congr (hP : VG.Proof.Blake2.X86.Stream.Ok P) {h0 : VG.Spec.Blake2.HashValue w} {mem mem' : Mem} {p : Addr} {d : List Byte}
    (hm : ∀ i < bufOff w + blockBytes w, mem' (p + BitVec.ofNat 64 i) = mem (p + BitVec.ofNat 64 i))
    (h : Spec.Blake2.Repr P h0 mem p d) : Spec.Blake2.Repr P h0 mem' p d := by
  rw [Proof.Blake2.repr_iff P hP.pos] at h ⊢
  exact VG.Proof.Blake2.X86.Stream.reprR_congr hP hm h

/-- The 32 bytes of stack below `E`, as the contracts write them. -/
theorem stk_eq {E : BitVec 32} (h : 32 ≤ E.toNat) : below E 32 = ⟨E.setWidth 64 - 32, 32⟩ := by
  simp only [below]; rw [Taint.sub_setWidth h]; rfl

/-! ## The number of bytes in the buffer -/

theorem or_beq_zero (a b : BitVec 32) : (a ||| b == 0) = decide ((a ++ b).toNat = 0) := by
  have h1 := VG.Proof.Blake2.X86.Stream.append_toNat_mod a b
  have h2 := VG.Proof.Blake2.X86.Stream.append_toNat_div a b
  by_cases h : (a ++ b).toNat = 0
  · have ha : a = 0 := BitVec.eq_of_toNat_eq (by rw [← h2, h]; rfl)
    have hb : b = 0 := BitVec.eq_of_toNat_eq (by rw [← h1, h]; rfl)
    simp [ha, hb]
  · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro hab
    obtain ⟨ha, hb⟩ := BitVec.or_eq_zero_iff.mp hab
    apply h
    rw [ha, hb]; rfl

theorem and_mask (hP : VG.Proof.Blake2.X86.Stream.Ok P) (x : BitVec 32) :
    x &&& BitVec.ofNat 32 (B w - 1) = BitVec.ofNat 32 (x.toNat % blockBytes w) := by
  rw [VG.Proof.Blake2.X86.Stream.B_eq]
  apply BitVec.eq_of_toNat_eq
  rcases hP.bb with h | h <;> rw [h] <;> simp only [BitVec.toNat_and, BitVec.toNat_ofNat]
  · rw [show (64 - 1) % 2 ^ 32 = 2 ^ 6 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]; omega
  · rw [show (128 - 1) % 2 ^ 32 = 2 ^ 7 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]; omega

theorem mask_ofNat (hP : VG.Proof.Blake2.X86.Stream.Ok P) {T : Nat} (hT : T ≠ 0) :
    ((BitVec.ofNat 32 T - 1) &&& BitVec.ofNat 32 (B w - 1)) + 1 =
      BitVec.ofNat 32 ((T - 1) % blockBytes w + 1) := by
  rw [VG.Proof.Blake2.X86.Stream.and_mask hP]
  apply BitVec.eq_of_toNat_eq
  have := hP.bb
  have h1 : (1 : BitVec 32).toNat = 1 := rfl
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, h1]
  rcases this with h | h <;> rw [h] <;> omega

/-! ## Our caller's registers, saved in `scratch[512..528)` -/

/-- Our caller's registers are saved in the scratch space at `scr`. -/
abbrev Saved (scr : BitVec 32) (s₀ : State) (m : Mem) : Prop := Spill.Saved m (addr scr) s₀.gpr saved

/-- The memory after saving them. -/
abbrev saveMem (scr : BitVec 32) (s₀ : State) : Mem := Spill.saveMem s₀.mem (addr scr) s₀.gpr saved

theorem saved_fits : Spill.Fits 528 saved := by decide

theorem saved_bound : ∀ p ∈ saved, 512 ≤ p.2 ∧ p.2 + 4 ≤ 528 := by decide

section
variable {scr : BitVec 32} (hfit : scr.toNat + 576 ≤ 2 ^ 32)
include hfit

theorem scr_contains {d n : Nat} (hd : d + n ≤ 576) (hn : 0 < n) :
    (⟨scr.setWidth 64, 576⟩ : Region).Contains (addr scr d) n :=
  MdStream.X86.contains_addr hd hn hfit

theorem rw_scr (m : Mem) (v : BitVec 32) {d e : Nat} (hd : d + 4 ≤ 576) (he : e + 4 ≤ 576)
    (h : d + 4 ≤ e ∨ e + 4 ≤ d) :
    (m.writeW (addr scr e) v).readW (addr scr d) 32 = m.readW (addr scr d) 32 :=
  MdStream.X86.readW_writeW_addr m v (by omega) (by omega) h

theorem saveMem_frame (s₀ : State) : Frame [⟨scr.setWidth 64, 576⟩] s₀.mem (VG.Proof.Blake2.X86.Stream.saveMem scr s₀) :=
  Spill.saveMem_frame List.mem_cons_self _ _ _ _ fun p h =>
    VG.Proof.Blake2.X86.Stream.scr_contains hfit (by have := VG.Proof.Blake2.X86.Stream.saved_bound p h; omega) (by omega)

theorem saveMem_saved (s₀ : State) : VG.Proof.Blake2.X86.Stream.Saved scr s₀ (VG.Proof.Blake2.X86.Stream.saveMem scr s₀) :=
  Spill.saveMem_saved_addr _ _ VG.Proof.Blake2.X86.Stream.saved_fits (by omega)

/-- A word of the scratch space from offset `d ≥ 512` on is kept by writes
elsewhere: to regions disjoint from the scratch space, or to its first 512
bytes. -/
theorem keep_hi {rs : List Region} {m m' : Mem} (hf : Frame (⟨scr.setWidth 64, 512⟩ :: rs) m m')
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨scr.setWidth 64, 576⟩ r) {d : Nat} (h₁ : 512 ≤ d) (h₂ : d + 4 ≤ 576) :
    m'.readW (addr scr d) 32 = m.readW (addr scr d) 32 := by
  refine hf.readW (r := ⟨addr scr d, 4⟩) (Region.contains_self _ _) ?_ (by decide)
  intro r hr
  simp only [List.mem_cons] at hr
  rcases hr with rfl | hr
  · rw [addr_eq (by omega)]; exact Offset.disjoint_base _ h₁ (by omega)
  · refine (hd r hr).sub_left ?_
    rw [addr_eq (by omega)]; exact MdStream.X86.sub_offset h₂ (by omega)

theorem Saved.keep {s₀ : State} {rs : List Region} {m m' : Mem} (h : VG.Proof.Blake2.X86.Stream.Saved scr s₀ m)
    (hf : Frame (⟨scr.setWidth 64, 512⟩ :: rs) m m')
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨scr.setWidth 64, 576⟩ r) : VG.Proof.Blake2.X86.Stream.Saved scr s₀ m' :=
  h.of_readW fun p hp => have := VG.Proof.Blake2.X86.Stream.saved_bound p hp; VG.Proof.Blake2.X86.Stream.keep_hi hfit hf hd this.1 (by omega)

end

/-- Restoring our caller's registers from the scratch space at `scr`, in `ebp`. -/
theorem restore_saved {s₀ s : State} {scr : BitVec 32} (hbp : s.gpr .ebp = scr)
    (hin : ∀ d, 512 ≤ d → d + 4 ≤ 528 → InRegions (s.rd ++ s.wr) (addr scr d) 4) (hsv : VG.Proof.Blake2.X86.Stream.Saved scr s₀ s.mem) :
    WP isa (.block restore) s fun s' =>
      (∀ r ∈ calleeSaved, r ≠ .esp → s'.gpr r = s₀.gpr r) ∧ s'.gpr .esp = s.gpr .esp ∧ s'.mem = s.mem := by
  rw [show restore = .mov .eax (.reg .ebp) :: (Spill.restoreCode .eax saved ++ []) from rfl]
  refine Wp.wp_mov fun s₁ u₁ => ?_
  have e₁ : s₁.gpr .eax = scr := by rw [u₁.gpr, hbp]
  refine Spill.restore_ok saved (by decide)
    (fun p h => by rw [e₁, u₁.rd, u₁.wr]; exact hin _ (VG.Proof.Blake2.X86.Stream.saved_bound p h).1 (VG.Proof.Blake2.X86.Stream.saved_bound p h).2)
    (by rw [e₁, u₁.mem]; exact hsv) fun s' r' =>
      WP.block_nil ⟨fun r hr hsp => r'.regs r (by revert hsp; revert hr; revert r; decide),
        by rw [r'.other _ (by decide), u₁.other _ (by decide)], by rw [r'.mem, u₁.mem]⟩

/-! ## The call -/

theorem frame_ne : [Reg.ebp, .eax, .edx, .ecx, .edi, .esi, .ebx] ≠ [] := by simp

theorem frame_esp : Reg.esp ∉ [Reg.ebp, .eax, .edx, .ecx, .edi, .esi, .ebx] := by decide

/-- Compressing the `k` blocks at `esi` (`blk`) into the state at `ebx`
(`st`), with the scratch space at `ebp` (`scr`), the counter in `edx:ecx` and
the final block flag in `eax`: a call of `compress(st, blk, k, t, last, scr)`
in a frame of its arguments, which uses the 32 bytes below `esp` (`E`) and
writes only there, the hash value and the first 512 bytes of the scratch
space. -/
theorem call_ok {name : String} {code : Prog isa} (hf : VG.Proof.Blake2.X86.Stream.CalleeOk P code) {s : State}
    {st scr blk E tlo thi lst : BitVec 32} {k : Nat}
    (hesp : s.gpr .esp = E) (hS : s.gpr .ebx = st) (hC : s.gpr .ebp = scr) (hB : s.gpr .esi = blk)
    (hk : (s.gpr .edi).toNat = k) (hlo : s.gpr .ecx = tlo) (hhi : s.gpr .edx = thi)
    (hl : s.gpr .eax = lst)
    (hE : 32 ≤ E.toNat) (f₀ : st.toNat + bufOff w ≤ 2 ^ 32) (f₁ : blk.toNat + blockBytes w * k ≤ 2 ^ 32)
    (f₃ : scr.toNat + 512 ≤ 2 ^ 32)
    (d₁ : Region.Disjoint ⟨st.setWidth 64, bufOff w⟩ ⟨scr.setWidth 64, 512⟩)
    (d₂ : Region.Disjoint ⟨blk.setWidth 64, blockBytes w * k⟩ ⟨st.setWidth 64, bufOff w⟩)
    (d₃ : Region.Disjoint ⟨blk.setWidth 64, blockBytes w * k⟩ ⟨scr.setWidth 64, 512⟩)
    (dS : Region.Disjoint (below E 32) ⟨st.setWidth 64, bufOff w⟩)
    (dC : Region.Disjoint (below E 32) ⟨scr.setWidth 64, 512⟩)
    (dB : Region.Disjoint (below E 32) ⟨blk.setWidth 64, blockBytes w * k⟩)
    (hc : Covers [⟨blk.setWidth 64, blockBytes w * k⟩] (s.rd ++ s.wr))
    (hw : Covers [⟨st.setWidth 64, bufOff w⟩, ⟨scr.setWidth 64, 512⟩] s.wr)
    {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame [⟨st.setWidth 64, bufOff w⟩, ⟨scr.setWidth 64, 512⟩, below E 32] s.mem s'.mem →
      VG.Spec.Blake2.stateAt w s'.mem (st.setWidth 64) =
        VG.Spec.Blake2.compressBlocks P (VG.Spec.Blake2.stateAt w s.mem (st.setWidth 64)) s.mem (blk.setWidth 64) k
          (thi ++ tlo).toNat (lst != 0) → Q s') :
    WP isa (compressCall name code) s Q := by
  have fit : 4 * [Reg.ebp, .eax, .edx, .ecx, .edi, .esi, .ebx].length + 4 ≤ (s.gpr .esp).toNat := by
    rw [hesp]; simp only [List.length_cons, List.length_nil]; omega
  have hrs := VG.Proof.Blake2.X86.Stream.frame_esp
  set sE := (pushed [Reg.ebp, .eax, .edx, .ecx, .edi, .esi, .ebx] s).callEntry with hsE
  have a0 : VG.X86.arg sE 0 = st := by rw [hsE, callEntry_arg fit hrs (by simp)]; simp [hS]
  have a1 : VG.X86.arg sE 1 = blk := by rw [hsE, callEntry_arg fit hrs (by simp)]; simp [hB]
  have a2 : (VG.X86.arg sE 2).toNat = k := by rw [hsE, callEntry_arg fit hrs (by simp)]; simp [hk]
  have a3 : VG.X86.arg sE 3 = tlo := by rw [hsE, callEntry_arg fit hrs (by simp)]; simp [hlo]
  have a4 : VG.X86.arg sE 4 = thi := by rw [hsE, callEntry_arg fit hrs (by simp)]; simp [hhi]
  have a5 : VG.X86.arg sE 5 = lst := by rw [hsE, callEntry_arg fit hrs (by simp)]; simp [hl]
  have a6 : VG.X86.arg sE 6 = scr := by rw [hsE, callEntry_arg fit hrs (by simp)]; simp [hC]
  have eA : argAddr sE 0 = (E - BitVec.ofNat 32 28).setWidth 64 := by
    rw [hsE, callEntry_argAddr0, hesp]; rfl
  have eSp : sE.gpr .esp = E - BitVec.ofNat 32 32 := by
    rw [hsE, callEntry_esp', hesp]; rfl
  have b28 : Region.Sub (below E 28) (below E 32) := below_sub (by omega) hE
  have r4 : Region.Sub ⟨(E - BitVec.ofNat 32 32).setWidth 64, 4⟩ (below E 32) := by
    have := below_inner (sp := E) (a := 4) (b := 32) (k := 28) (by omega) hE
    rw [show E - BitVec.ofNat 32 32 = E - BitVec.ofNat 32 28 - BitVec.ofNat 32 4 by
      rw [← VG.Offset.sub_add_eq]; rfl]
    exact this
  refine WP.callWith (k := compressX86 P) hf.verified hf.nosp VG.Proof.Blake2.X86.Stream.frame_ne hrs
    (by rw [hf.stack, hesp]; simp only [List.length_cons, List.length_nil]; omega)
    (rd := [⟨blk.setWidth 64, blockBytes w * k⟩, ⟨argAddr sE 0, 28⟩])
    (wr := [⟨st.setWidth 64, 8 * (w / 8)⟩, ⟨scr.setWidth 64, 512⟩])
    ⟨?_, ?_, ?_⟩ fun s' rd' wr' cs' f' ⟨s₂, m₂, post⟩ => ?_
  · rw [← hsE]
    simp only [compressX86, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr,
      arg_withRegions, argAddr_withRegions, a0, a1, a2, a6, eA, eSp]
    refine ⟨trivial, trivial, d₁, d₂, d₃, dS.sub_left b28, dC.sub_left b28,
      dS.sub_left r4, dC.sub_left r4, f₀, f₁, f₃, ?_⟩
    rw [sub_toNat hE]; have := E.isLt; omega
  · rw [hesp]
    intro a n ⟨r, hr, hcn⟩
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · obtain ⟨r', hr', hc'⟩ := hc a n ⟨_, List.mem_singleton_self _, by simpa using hcn⟩
      exact InRegions_append_cons.mpr (.inr ⟨r', hr', hc'⟩)
    · refine InRegions_append_cons.mpr (.inl ?_)
      rw [eA] at hcn
      simp only [Region.Contains] at hcn ⊢
      simpa using hcn
    · obtain ⟨r', hr', hc'⟩ := hw a n ⟨_, by simp, hcn⟩
      exact InRegions_append_cons.mpr (.inr ⟨r', List.mem_append_right _ hr', hc'⟩)
    · obtain ⟨r', hr', hc'⟩ := hw a n ⟨_, by simp, hcn⟩
      exact InRegions_append_cons.mpr (.inr ⟨r', List.mem_append_right _ hr', hc'⟩)
  · rw [hesp]
    intro a n ⟨r, hr, hcn⟩
    obtain ⟨r', hr', hc'⟩ := hw a n ⟨r, hr, hcn⟩
    exact ⟨r', List.mem_cons_of_mem _ hr', hc'⟩
  · rw [hf.stack, hesp] at f'
    have hsE' : Frame [below E 32] s.mem sE.mem := by
      have := callEntry_frame fit hrs
      rw [hesp] at this; exact this
    rw [← hsE] at post
    simp only [compressX86, arg_withRegions, State.withRegions_mem, a0, a1, a2, a3, a4, a5, m₂] at post
    refine hQ s' rd' wr' cs' f' ?_
    have e₁ : VG.Spec.Blake2.stateAt w sE.mem (st.setWidth 64) = VG.Spec.Blake2.stateAt w s.mem (st.setWidth 64) :=
      stateAt_congr fun i hi =>
        hsE'.bytes (R := ⟨st.setWidth 64, bufOff w⟩) (by simpa using dS.symm) (by simp; omega) hi
    have e₂ : VG.Spec.Blake2.compressBlocks P (VG.Spec.Blake2.stateAt w s.mem (st.setWidth 64)) sE.mem (blk.setWidth 64) k
          (thi ++ tlo).toNat (lst != 0) =
        VG.Spec.Blake2.compressBlocks P (VG.Spec.Blake2.stateAt w s.mem (st.setWidth 64)) s.mem (blk.setWidth 64) k
          (thi ++ tlo).toNat (lst != 0) :=
      compressBlocks_congr P fun j hj =>
        hsE'.bytes (R := ⟨blk.setWidth 64, blockBytes w * k⟩) (by simpa using dB.symm) (by simp; omega) hj
    rw [post, e₁, e₂]

/-! ## Copying bytes into the buffer -/

theorem contains_prefix (q : Addr) {j k : Nat} (h : j ≤ k) : (⟨q, k⟩ : Region).Contains q j := by
  simp [Region.Contains, h]

/-- The copy loop's state after `j` of `k` bytes, from `s₀`. -/
structure CopyI (s₀ : State) (src dst cnt tmp : Reg) (dA sA : BitVec 32) (k j : Nat) (s : State) : Prop where
  j_le : j ≤ k
  srcV : s.gpr src = sA + BitVec.ofNat 32 j
  dstV : s.gpr dst = dA + BitVec.ofNat 32 j
  cntV : s.gpr cnt = BitVec.ofNat 32 (k - j)
  other : ∀ x, x ≠ src → x ≠ dst → x ≠ cnt → x ≠ tmp → s.gpr x = s₀.gpr x
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : s.mem = VG.WriteBytes.writeBytes s₀.mem (addr dA (bufOff w))
    ((VG.Spec.Blake2.bytesAt s₀.mem (sA.setWidth 64) k).take j)

/-- The loop copying `k ≥ 1` bytes from `sA` (at `src`) to `dA + N` (at `dst`),
with the count in `cnt` and the bytes through `tmp`: neither the source nor
the destination wraps around the (32-bit) address space, and they do not
overlap. -/
theorem copyLoop_ok {src dst cnt : Reg} {tmp : Reg8} (h₁ : src ≠ dst) (h₂ : src ≠ cnt)
    (h₃ : dst ≠ cnt) (h₄ : tmp.reg ≠ src) (h₅ : tmp.reg ≠ dst) (h₆ : tmp.reg ≠ cnt)
    {s₀ : State} {dA sA : BitVec 32} {k : Nat} (hk : 1 ≤ k) (hk32 : k < 2 ^ 32)
    (hfs : sA.toNat + k ≤ 2 ^ 32) (hfd : dA.toNat + bufOff w + k ≤ 2 ^ 32)
    (hsrc : s₀.gpr src = sA) (hdst : s₀.gpr dst = dA) (hcnt : s₀.gpr cnt = BitVec.ofNat 32 k)
    (hin : ∀ i < k, InRegions (s₀.rd ++ s₀.wr) (sA.setWidth 64 + BitVec.ofNat 64 i) 1)
    (hout : ∀ i < k, InRegions s₀.wr (addr dA (bufOff w) + BitVec.ofNat 64 i) 1)
    (hd : Region.Disjoint ⟨sA.setWidth 64, k⟩ ⟨addr dA (bufOff w), k⟩)
    {Q : State → Prop} (hQ : ∀ s, VG.Proof.Blake2.X86.Stream.CopyI (w := w) s₀ src dst cnt tmp.reg dA sA k k s → Q s) :
    WP isa (copyLoop w src dst cnt tmp) s₀ Q := by
  refine WP.loop (M := isa) (fun n (s : State) => ∃ j, n = k - j ∧ j < k ∧
      VG.Proof.Blake2.X86.Stream.CopyI (w := w) s₀ src dst cnt tmp.reg dA sA k j s) ?_ k s₀
    ⟨0, by omega, by omega, by omega, by simp [hsrc], by simp [hdst], by rw [hcnt, Nat.sub_zero],
      fun _ _ _ _ _ => rfl, rfl, rfl, by rw [List.take_zero, VG.WriteBytes.writeBytes_nil]⟩
  rintro n s ⟨j, rfl, hj, h⟩
  have hxs : (VG.Spec.Blake2.bytesAt s₀.mem (sA.setWidth 64) k).length = k := by simp [VG.Spec.Blake2.bytesAt]
  -- The addresses.
  have eS : addr (s.gpr src) 0 = sA.setWidth 64 + BitVec.ofNat 64 j := by
    rw [h.srcV, MdStream.X86.addr_add_ofNat (by omega), Nat.add_zero]
  have eD : addr (s.gpr dst) (bufOff w) = addr dA (bufOff w) + BitVec.ofNat 64 j := by
    rw [h.dstV, MdStream.X86.addr_add_ofNat (by omega), addr_eq (by omega), BitVec.add_assoc,
      BitVec.ofNat_add, BitVec.add_comm (BitVec.ofNat 64 j)]
  -- The byte read.
  have hin' : InRegions (s.rd ++ s.wr) (sA.setWidth 64 + BitVec.ofNat 64 j) 1 := by
    rw [h.rd, h.wr]; exact hin j hj
  have hbyte : s.mem (sA.setWidth 64 + BitVec.ofNat 64 j) = s₀.mem (sA.setWidth 64 + BitVec.ofNat 64 j) := by
    rw [h.mem]
    exact (VG.WriteBytes.writeBytes_frame s₀.mem _ _ (VG.Proof.Blake2.X86.Stream.contains_prefix (k := k) _ (by simp; omega))).bytes
      (R := ⟨sA.setWidth 64, k⟩) (by simpa using hd) (by show k ≤ 2 ^ 64; omega) hj
  have hout' : InRegions s.wr (addr dA (bufOff w) + BitVec.ofNat 64 j) 1 := by
    rw [h.wr]; exact hout j hj
  refine cons (s' := s.setReg tmp.reg ((s.mem (sA.setWidth 64 + BitVec.ofNat 64 j)).setWidth 32))
    (by simp [exec, State.load8, ea_mk, at_, eS, hin']) ?_
  set s₁ := s.setReg tmp.reg ((s.mem (sA.setWidth 64 + BitVec.ofNat 64 j)).setWidth 32) with hs₁
  have g₁ : ∀ x, x ≠ tmp.reg → s₁.gpr x = s.gpr x := fun x hx => RegUpd.gpr_setReg_of_ne _ _ hx
  set m₂ := s₁.mem.writeW (addr dA (bufOff w) + BitVec.ofNat 64 j) ((s₁.gpr tmp.reg).setWidth 8) with hm₂
  refine cons (s' := { s₁ with mem := m₂ }) ?_ ?_
  · have e : s₁.ea (at_ dst (VG.Impl.Blake2.X86.Stream.N w)) = addr dA (bufOff w) + BitVec.ofNat 64 j := by
      show addr (s₁.gpr dst) (VG.Impl.Blake2.X86.Stream.N w) = _
      rw [g₁ _ (Ne.symm h₅)]; exact eD
    have hw₁ : InRegions s₁.wr (addr dA (bufOff w) + BitVec.ofNat 64 j) 1 := hout'
    simp only [exec, State.store8, e, hw₁, ite_true, hm₂]
  refine wp_addi fun s₃ u₃ => wp_addi fun s₄ u₄ => wp_subi fun s₅ u₅ _ hz₅ => WP.block_nil ?_
  have g : ∀ x, x ≠ cnt → x ≠ dst → x ≠ src → x ≠ tmp.reg → s₅.gpr x = s.gpr x := fun x a b c d => by
    rw [u₅.other x a, u₄.other x b, u₃.other x c]; exact g₁ x d
  have hcnt' : s₅.gpr cnt = BitVec.ofNat 32 (k - (j + 1)) := by
    rw [u₅.gpr, u₄.other _ (Ne.symm h₃), u₃.other _ (Ne.symm h₂), show s₁.gpr cnt = s.gpr cnt from
      g₁ _ (Ne.symm h₆), h.cntV, ofNat_pred (by omega), Nat.sub_sub]
  have hI : VG.Proof.Blake2.X86.Stream.CopyI (w := w) s₀ src dst cnt tmp.reg dA sA k (j + 1) s₅ := by
    refine ⟨by omega, ?_, ?_, hcnt', fun x a b c d => ?_, ?_, ?_, ?_⟩
    · rw [u₅.other _ h₂, u₄.other _ h₁, u₃.gpr, show s₁.gpr src = s.gpr src from g₁ _ (Ne.symm h₄),
        h.srcV, BitVec.add_assoc, BitVec.ofNat_add]; rfl
    · rw [u₅.other _ h₃, u₄.gpr, u₃.other _ (Ne.symm h₁), show s₁.gpr dst = s.gpr dst from
        g₁ _ (Ne.symm h₅), h.dstV, BitVec.add_assoc, BitVec.ofNat_add]; rfl
    · rw [g x c b a d, h.other x a b c d]
    · rw [u₅.rd, u₄.rd, u₃.rd]; exact h.rd
    · rw [u₅.wr, u₄.wr, u₃.wr]; exact h.wr
    · have hj' : j < (VG.Spec.Blake2.bytesAt s₀.mem (sA.setWidth 64) k).length := by omega
      have hlen : (List.take j (VG.Spec.Blake2.bytesAt s₀.mem (sA.setWidth 64) k)).length < 2 ^ 64 := by
        simp only [List.length_take]; omega
      rw [u₅.mem, u₄.mem, u₃.mem]
      show s₁.mem.writeW _ ((s₁.gpr tmp.reg).setWidth 8) = _
      rw [hs₁, RegUpd.mem_setReg, RegUpd.gpr_setReg_self, hbyte, h.mem, List.take_add_one,
        List.getElem?_eq_getElem hj', Option.toList_some, VG.WriteBytes.writeBytes_snoc _ _ _ _ hlen]
      have hl : (List.take j (VG.Spec.Blake2.bytesAt s₀.mem (sA.setWidth 64) k)).length = j := by
        rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hj')]
      rw [hl, BitVec.setWidth_setWidth_of_le _ (by omega), BitVec.setWidth_eq]
      congr 1
      simp [VG.Spec.Blake2.bytesAt]
  have hzf : s₅.zf = some (decide (k - (j + 1) = 0)) := by
    rw [hz₅, u₄.other _ (Ne.symm h₃), u₃.other _ (Ne.symm h₂), show s₁.gpr cnt = s.gpr cnt from
      g₁ _ (Ne.symm h₆), h.cntV, ofNat_pred (show 1 ≤ k - j by omega), ofNat_beq_zero (by omega),
      show k - j - 1 = k - (j + 1) by omega]
  by_cases hjk : j + 1 = k
  · refine .inl ⟨?_, hQ _ (hjk ▸ hI)⟩
    simp only [VG.X86.eval, hzf, show k - (j + 1) = 0 by omega, decide_true, Option.map_some, Bool.not_true]
  · refine .inr ⟨?_, k - (j + 1), by omega, j + 1, rfl, by omega, hI⟩
    simp only [VG.X86.eval, hzf, show k - (j + 1) ≠ 0 by omega, decide_false, Option.map_some, Bool.not_false]

end VG.Proof.Blake2.X86.Stream

end

/- Proofs formerly in `VerifiedGarbage.Proof.Blake2.X86.Stream.Finalize`. -/
section

/-!
# Streaming BLAKE2 on x86 (32-bit): `finalize`

`finalize` saves the callee-saved registers (`prologue_ok`), computes the
number of buffered bytes (`bufLen_val`), zeroes the rest of the buffer
(`pad_ok`), compresses it as the last block (`call_ok`), copies the hash value
out (`output_ok`) and restores the registers (`epilogue_ok`), for either word
size and any correct compression function (`CalleeOk`).
-/

namespace VG.Proof.Blake2.X86.Stream.Finalize

open VG VG.X86 VG.X86.Wp VG.Spec.Blake2
open VG.Impl.Blake2.X86 (at_)
open VG.Impl.Blake2.X86.Stream
open VG.Proof.Blake2 (compressX86 finalizeX86 countX86 final_eq stateAt_congr bytesAt_congr bytesAt_add
  bytesAt_state wordBytes_readW bufLen_le compressBlocks_succ compressBlocks_zero)
open VG.WriteBytes (writeBytes writeBytes_nil writeBytes_snoc writeBytes_frame writeBytes_append
  writeBytes_before write_eq_writeBytes)
open VG.Proof.MdStream.X86 (contains_addr sub_offset contains_offset)

variable {w : Nat} {P : VG.Spec.Blake2.Params w}

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev esp₀ : BitVec 32 := s₀.gpr .esp
abbrev st : BitVec 32 := VG.X86.arg s₀ 0
abbrev cnt : Nat := (countX86 s₀).toNat
abbrev op : BitVec 32 := VG.X86.arg s₀ 3
abbrev scr : BitVec 32 := VG.X86.arg s₀ 4
abbrev stA : Addr := (VG.Proof.Blake2.X86.Stream.Finalize.st s₀).setWidth 64
abbrev opA : Addr := (VG.Proof.Blake2.X86.Stream.Finalize.op s₀).setWidth 64
abbrev scA : Addr := (VG.Proof.Blake2.X86.Stream.Finalize.scr s₀).setWidth 64
abbrev stR (w : Nat) : Region := ⟨VG.Proof.Blake2.X86.Stream.Finalize.stA s₀, bufOff w + blockBytes w⟩
abbrev outR (w : Nat) : Region := ⟨VG.Proof.Blake2.X86.Stream.Finalize.opA s₀, bufOff w⟩
abbrev scR : Region := ⟨VG.Proof.Blake2.X86.Stream.Finalize.scA s₀, 576⟩
abbrev argR : Region := ⟨argAddr s₀ 0, 20⟩
abbrev retR : Region := ⟨(VG.Proof.Blake2.X86.Stream.Finalize.esp₀ s₀).setWidth 64, 4⟩
/-- Where the call of the compression function pushes its arguments and
stores the return address. -/
abbrev stkR : Region := below (VG.Proof.Blake2.X86.Stream.Finalize.esp₀ s₀) 32

end

structure Pre (w : Nat) (s₀ : State) : Prop where
  rd : s₀.rd = [VG.Proof.Blake2.X86.Stream.Finalize.argR s₀]
  wr : s₀.wr = [VG.Proof.Blake2.X86.Stream.Finalize.stR s₀ w, VG.Proof.Blake2.X86.Stream.Finalize.outR s₀ w, VG.Proof.Blake2.X86.Stream.Finalize.scR s₀]
  st_out : (VG.Proof.Blake2.X86.Stream.Finalize.stR s₀ w).Disjoint (VG.Proof.Blake2.X86.Stream.Finalize.outR s₀ w)
  st_scr : (VG.Proof.Blake2.X86.Stream.Finalize.stR s₀ w).Disjoint (VG.Proof.Blake2.X86.Stream.Finalize.scR s₀)
  out_scr : (VG.Proof.Blake2.X86.Stream.Finalize.outR s₀ w).Disjoint (VG.Proof.Blake2.X86.Stream.Finalize.scR s₀)
  a_st : (VG.Proof.Blake2.X86.Stream.Finalize.argR s₀).Disjoint (VG.Proof.Blake2.X86.Stream.Finalize.stR s₀ w)
  a_out : (VG.Proof.Blake2.X86.Stream.Finalize.argR s₀).Disjoint (VG.Proof.Blake2.X86.Stream.Finalize.outR s₀ w)
  a_scr : (VG.Proof.Blake2.X86.Stream.Finalize.argR s₀).Disjoint (VG.Proof.Blake2.X86.Stream.Finalize.scR s₀)
  ret_st : (VG.Proof.Blake2.X86.Stream.Finalize.retR s₀).Disjoint (VG.Proof.Blake2.X86.Stream.Finalize.stR s₀ w)
  ret_out : (VG.Proof.Blake2.X86.Stream.Finalize.retR s₀).Disjoint (VG.Proof.Blake2.X86.Stream.Finalize.outR s₀ w)
  ret_scr : (VG.Proof.Blake2.X86.Stream.Finalize.retR s₀).Disjoint (VG.Proof.Blake2.X86.Stream.Finalize.scR s₀)
  stk_st : (VG.Proof.Blake2.X86.Stream.Finalize.stkR s₀).Disjoint (VG.Proof.Blake2.X86.Stream.Finalize.stR s₀ w)
  stk_out : (VG.Proof.Blake2.X86.Stream.Finalize.stkR s₀).Disjoint (VG.Proof.Blake2.X86.Stream.Finalize.outR s₀ w)
  stk_scr : (VG.Proof.Blake2.X86.Stream.Finalize.stkR s₀).Disjoint (VG.Proof.Blake2.X86.Stream.Finalize.scR s₀)
  st_fit : (VG.Proof.Blake2.X86.Stream.Finalize.st s₀).toNat + (bufOff w + blockBytes w) ≤ 2 ^ 32
  out_fit : (VG.Proof.Blake2.X86.Stream.Finalize.op s₀).toNat + bufOff w ≤ 2 ^ 32
  scr_fit : (VG.Proof.Blake2.X86.Stream.Finalize.scr s₀).toNat + 576 ≤ 2 ^ 32
  sp_lo : 32 ≤ (VG.Proof.Blake2.X86.Stream.Finalize.esp₀ s₀).toNat
  sp_fit : (VG.Proof.Blake2.X86.Stream.Finalize.esp₀ s₀).toNat + 24 ≤ 2 ^ 32

theorem pre_of {s₀ : State} (h : (finalizeX86 P).pre s₀) : VG.Proof.Blake2.X86.Stream.Finalize.Pre w s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19⟩ := h
  have e := VG.Proof.Blake2.X86.Stream.stk_eq h18
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
    by show (below _ _).Disjoint _; rw [e]; exact h12, by show (below _ _).Disjoint _; rw [e]; exact h13,
    by show (below _ _).Disjoint _; rw [e]; exact h14, h15, h16, h17, h18, h19⟩

namespace Pre
variable {s₀ : State} (hp : VG.Proof.Blake2.X86.Stream.Finalize.Pre w s₀)
include hp

theorem scr_in {d : Nat} (hd : d + 4 ≤ 576) : (VG.Proof.Blake2.X86.Stream.Finalize.scR s₀).Contains (addr (VG.Proof.Blake2.X86.Stream.Finalize.scr s₀) d) 4 :=
  contains_addr hd (by omega) hp.scr_fit

theorem arg_in {d : Nat} (hd₁ : 4 ≤ d) (hd : d + 4 ≤ 24) : (VG.Proof.Blake2.X86.Stream.Finalize.argR s₀).Contains (addr (VG.Proof.Blake2.X86.Stream.Finalize.esp₀ s₀) d) 4 := by
  have := hp.sp_fit
  show (⟨addr (VG.Proof.Blake2.X86.Stream.Finalize.esp₀ s₀) 4, 20⟩ : Region).Contains _ _
  rw [addr_eq (by omega), addr_eq (by omega)]
  exact Offset.contains _ hd₁ (by omega) (by omega)

theorem rin {s : State} (hrd : s.rd = s₀.rd) {d : Nat} (h₁ : 4 ≤ d) (h₂ : d + 4 ≤ 24) :
    InRegions (s.rd ++ s.wr) (addr (VG.Proof.Blake2.X86.Stream.Finalize.esp₀ s₀) d) 4 :=
  ⟨VG.Proof.Blake2.X86.Stream.Finalize.argR s₀, by simp [hrd, hp.rd], hp.arg_in h₁ h₂⟩

theorem sin {s : State} (hwr : s.wr = s₀.wr) {d : Nat} (hd : d + 4 ≤ 576) :
    InRegions s.wr (addr (VG.Proof.Blake2.X86.Stream.Finalize.scr s₀) d) 4 :=
  ⟨VG.Proof.Blake2.X86.Stream.Finalize.scR s₀, by simp [hwr, hp.wr], hp.scr_in hd⟩

theorem sinr {s : State} (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) {d : Nat} (hd : d + 4 ≤ 576) :
    InRegions (s.rd ++ s.wr) (addr (VG.Proof.Blake2.X86.Stream.Finalize.scr s₀) d) 4 :=
  ⟨VG.Proof.Blake2.X86.Stream.Finalize.scR s₀, by simp [hrd, hwr, hp.wr], hp.scr_in hd⟩

theorem ret_stk : (VG.Proof.Blake2.X86.Stream.Finalize.retR s₀).Disjoint (VG.Proof.Blake2.X86.Stream.Finalize.stkR s₀) := by
  have := hp.sp_fit; have := hp.sp_lo
  show Region.Disjoint ⟨(VG.Proof.Blake2.X86.Stream.Finalize.esp₀ s₀).setWidth 64, 4⟩ ⟨(VG.Proof.Blake2.X86.Stream.Finalize.esp₀ s₀ - BitVec.ofNat 32 32).setWidth 64, 32⟩
  rw [Taint.sub_setWidth (by omega)]
  exact Offset.base_disjoint_below _ (by omega)

theorem a_stk : (VG.Proof.Blake2.X86.Stream.Finalize.argR s₀).Disjoint (VG.Proof.Blake2.X86.Stream.Finalize.stkR s₀) := by
  have := hp.sp_fit; have := hp.sp_lo
  show Region.Disjoint ⟨addr (VG.Proof.Blake2.X86.Stream.Finalize.esp₀ s₀) 4, 20⟩ ⟨(VG.Proof.Blake2.X86.Stream.Finalize.esp₀ s₀ - BitVec.ofNat 32 32).setWidth 64, 32⟩
  rw [addr_eq (by omega), Taint.sub_setWidth (by omega)]
  exact Offset.disjoint_below _ (by omega)

theorem arg_sub {d : Nat} (hd₁ : 4 ≤ d) (hd : d + 4 ≤ 24) : Region.Sub ⟨addr (VG.Proof.Blake2.X86.Stream.Finalize.esp₀ s₀) d, 4⟩ (VG.Proof.Blake2.X86.Stream.Finalize.argR s₀) := by
  have := hp.sp_fit
  show Region.Sub _ ⟨addr (VG.Proof.Blake2.X86.Stream.Finalize.esp₀ s₀) 4, 20⟩
  rw [addr_eq (by omega), addr_eq (by omega)]
  exact Offset.sub _ hd₁ (by omega)

end Pre

/-! ## The prologue -/

/-- After the prologue. -/
structure Start (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  ebx : s.gpr .ebx = VG.Proof.Blake2.X86.Stream.Finalize.st s₀
  ebp : s.gpr .ebp = VG.Proof.Blake2.X86.Stream.Finalize.scr s₀
  esp : s.gpr .esp = VG.Proof.Blake2.X86.Stream.Finalize.esp₀ s₀
  eax : s.gpr .eax = VG.X86.arg s₀ 1
  ecx : s.gpr .ecx = VG.X86.arg s₀ 2
  mem : s.mem = VG.Proof.Blake2.X86.Stream.saveMem (VG.Proof.Blake2.X86.Stream.Finalize.scr s₀) s₀

theorem prologue_ok {s₀ : State} (hp : VG.Proof.Blake2.X86.Stream.Finalize.Pre w s₀) : WP isa (.block finalizeStart) s₀ (VG.Proof.Blake2.X86.Stream.Finalize.Start s₀) := by
  have rin : ∀ {d}, 4 ≤ d → d + 4 ≤ 24 → InRegions (s₀.rd ++ s₀.wr) (addr (VG.Proof.Blake2.X86.Stream.Finalize.esp₀ s₀) d) 4 :=
    fun h₁ h₂ => hp.rin rfl h₁ h₂
  have sin : ∀ {d}, d + 4 ≤ 576 → InRegions s₀.wr (addr (VG.Proof.Blake2.X86.Stream.Finalize.scr s₀) d) 4 := fun h => hp.sin rfl h
  have sepA : ∀ d e, 512 ≤ d → d + 4 ≤ 576 → 4 ≤ e → e + 4 ≤ 24 →
      Mem.Sep (addr (VG.Proof.Blake2.X86.Stream.Finalize.esp₀ s₀) e) 4 (addr (VG.Proof.Blake2.X86.Stream.Finalize.scr s₀) d) 4 := by
    intro d e h₁ h₂ h₃ h₄
    exact hp.a_scr.sep (hp.arg_in h₃ h₄) (hp.scr_in h₂)
  have argSave : ∀ e, 4 ≤ e → e + 4 ≤ 24 →
      (VG.Proof.Blake2.X86.Stream.saveMem (VG.Proof.Blake2.X86.Stream.Finalize.scr s₀) s₀).readW (addr (VG.Proof.Blake2.X86.Stream.Finalize.esp₀ s₀) e) 32 = s₀.mem.readW (addr (VG.Proof.Blake2.X86.Stream.Finalize.esp₀ s₀) e) 32 := by
    intro e h₁ h₂
    exact Spill.saveMem_readW_of_sep _ _ (by decide) _ _ fun p h =>
      have := VG.Proof.Blake2.X86.Stream.saved_bound p h; sepA _ e this.1 (by omega) h₁ h₂
  rw [show finalizeStart = .mov .eax (.mem (at_ .esp 20)) :: (Spill.saveCode .eax saved ++
    ([.mov .ebp (.reg .eax), .mov .ebx (.mem (at_ .esp 4)), .mov .eax (.mem (at_ .esp 8)),
      .mov .ecx (.mem (at_ .esp 12))] : List Instr)) from rfl]
  refine wp_ldm (B := VG.Proof.Blake2.X86.Stream.Finalize.esp₀ s₀) rfl (rin (d := 20) (by omega) (by omega)) fun s₁ u₁ => ?_
  have e₁ : s₁.gpr .eax = VG.Proof.Blake2.X86.Stream.Finalize.scr s₀ := u₁.gpr
  refine Spill.save_ok saved (fun p h => by
    rw [e₁, u₁.wr]; exact sin (by have := VG.Proof.Blake2.X86.Stream.saved_bound p h; omega)) fun s₅ u₅ => ?_
  have g₅ : s₅.gpr = s₁.gpr := u₅.gpr
  have m₅ : s₅.mem = VG.Proof.Blake2.X86.Stream.saveMem (VG.Proof.Blake2.X86.Stream.Finalize.scr s₀) s₀ := by
    rw [u₅.mem, e₁, u₁.mem]
    exact Spill.saveMem_congr _ _ (fun _ _ => rfl) fun p h => u₁.other _ (by revert p h; decide)
  have rd₅ : s₅.rd = s₀.rd := by rw [u₅.rd, u₁.rd]
  have wr₅ : s₅.wr = s₀.wr := by rw [u₅.wr, u₁.wr]
  have sp₅ : s₅.gpr .esp = VG.Proof.Blake2.X86.Stream.Finalize.esp₀ s₀ := by rw [g₅, u₁.other _ (by decide)]
  refine wp_mov fun s₆ u₆ => ?_
  have sp₆ : s₆.gpr .esp = VG.Proof.Blake2.X86.Stream.Finalize.esp₀ s₀ := by rw [u₆.other _ (by decide), sp₅]
  have rd' : ∀ d, 4 ≤ d → d + 4 ≤ 24 → InRegions (s₆.rd ++ s₆.wr) (addr (VG.Proof.Blake2.X86.Stream.Finalize.esp₀ s₀) d) 4 :=
    fun d h₁ h₂ => by rw [u₆.rd, u₆.wr, rd₅, wr₅]; exact rin h₁ h₂
  have l : ∀ e, 4 ≤ e → e + 4 ≤ 24 → s₆.mem.readW (addr (VG.Proof.Blake2.X86.Stream.Finalize.esp₀ s₀) e) 32 = s₀.mem.readW (addr (VG.Proof.Blake2.X86.Stream.Finalize.esp₀ s₀) e) 32 :=
    fun e h₁ h₂ => by rw [u₆.mem, m₅]; exact argSave e h₁ h₂
  refine wp_ldm sp₆ (rd' 4 (by omega) (by omega)) fun s₇ u₇ => ?_
  refine wp_ldm (by rw [u₇.other _ (by decide), sp₆]) (by rw [u₇.rd, u₇.wr]; exact rd' 8 (by omega) (by omega))
    fun s₈ u₈ => ?_
  refine wp_ldm (by rw [u₈.other _ (by decide), u₇.other _ (by decide), sp₆])
    (by rw [u₈.rd, u₈.wr, u₇.rd, u₇.wr]; exact rd' 12 (by omega) (by omega)) fun s₉ u₉ => WP.block_nil ?_
  refine ⟨by rw [u₉.rd, u₈.rd, u₇.rd, u₆.rd, rd₅], by rw [u₉.wr, u₈.wr, u₇.wr, u₆.wr, wr₅], ?_, ?_, ?_, ?_, ?_,
    by rw [u₉.mem, u₈.mem, u₇.mem, u₆.mem, m₅]⟩
  · rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr, l 4 (by omega) (by omega)]; rfl
  · rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, g₅, e₁]
  · rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), sp₆]
  · rw [u₉.other _ (by decide), u₈.gpr, u₇.mem, l 8 (by omega) (by omega)]; rfl
  · rw [u₉.gpr, u₈.mem, u₇.mem, l 12 (by omega) (by omega)]; rfl

/-! ## The number of buffered bytes -/

theorem bufLen_val (hP : VG.Proof.Blake2.X86.Stream.Ok P) {s : State} {lo hi : BitVec 32} (hax : s.gpr .eax = lo)
    (hcx : s.gpr .ecx = hi) :
    WP isa (Impl.Blake2.X86.Stream.bufLen w) s fun s' =>
      s'.gpr .eax = BitVec.ofNat 32 (Proof.Blake2.bufLen w (hi ++ lo).toNat) ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  unfold Impl.Blake2.X86.Stream.bufLen
  refine WP.seq (VG.Proof.Blake2.X86.Stream.wp_orZ fun s₁ u₁ z₁ => WP.block_nil ?_)
  have hz : isa.eval .e s₁ = some (decide ((hi ++ lo).toNat = 0)) := by
    show s₁.zf = _
    rw [z₁, hcx, hax, VG.Proof.Blake2.X86.Stream.or_beq_zero]
  refine WP.ite _ hz (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    refine wp_movi fun s₂ u₂ => WP.block_nil ⟨?_, fun r h1 h2 => by rw [u₂.other r h1, u₁.other r h2],
      by rw [u₂.mem, u₁.mem], by rw [u₂.rd, u₁.rd], by rw [u₂.wr, u₁.wr]⟩
    rw [u₂.gpr, hb]; rfl
  · simp only [decide_eq_false_iff_not] at hb
    refine wp_subi fun s₂ u₂ _ _ => wp_andi fun s₃ u₃ => wp_addi fun s₄ u₄ => WP.block_nil
      ⟨?_, fun r h1 h2 => by rw [u₄.other r h1, u₃.other r h1, u₂.other r h1, u₁.other r h2],
        by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem], by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd],
        by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]⟩
    have e : lo = BitVec.ofNat 32 (hi ++ lo).toNat := (VG.Proof.Blake2.X86.Stream.lo_append hi lo).symm
    rw [u₄.gpr, u₃.gpr, u₂.gpr, u₁.other _ (by decide), hax]
    conv_lhs => rw [e]
    rw [VG.Proof.Blake2.X86.Stream.mask_ofNat hP hb]
    simp only [Proof.Blake2.bufLen, hb, ite_false]

/-! ## Zeroing the rest of the buffer -/

/-- The zeroing loop's state after `j` of `k` bytes, from `s₀`. -/
structure ZI (s₀ : State) (dA : BitVec 32) (k j : Nat) (s : State) : Prop where
  j_le : j ≤ k
  edx : s.gpr .edx = dA + BitVec.ofNat 32 j
  ecx : s.gpr .ecx = BitVec.ofNat 32 (k - j)
  other : ∀ x, x ≠ .edx → x ≠ .ecx → s.gpr x = s₀.gpr x
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : s.mem = VG.WriteBytes.writeBytes s₀.mem (addr dA (bufOff w)) (List.replicate j 0)

/-- The loop zeroing `k ≥ 1` bytes at `dA + N` (at `edx`, `eax = 0`). -/
theorem zeroLoop_ok {s₀ : State} {dA : BitVec 32} {k : Nat} (hk : 1 ≤ k) (hk32 : k < 2 ^ 32)
    (hfd : dA.toNat + bufOff w + k ≤ 2 ^ 32)
    (hdx : s₀.gpr .edx = dA) (hcx : s₀.gpr .ecx = BitVec.ofNat 32 k) (hax : s₀.gpr .eax = 0)
    (hout : ∀ i < k, InRegions s₀.wr (addr dA (bufOff w) + BitVec.ofNat 64 i) 1)
    {Q : State → Prop} (hQ : ∀ s, VG.Proof.Blake2.X86.Stream.Finalize.ZI (w := w) s₀ dA k k s → Q s) :
    WP isa (zeroLoop w) s₀ Q := by
  refine WP.loop (M := isa) (fun n (s : State) => ∃ j, n = k - j ∧ j < k ∧ VG.Proof.Blake2.X86.Stream.Finalize.ZI (w := w) s₀ dA k j s) ?_ k s₀
    ⟨0, by omega, by omega, by omega, by simp [hdx], by rw [hcx, Nat.sub_zero], fun _ _ _ => rfl, rfl, rfl,
      by rw [List.replicate_zero, VG.WriteBytes.writeBytes_nil]⟩
  rintro n s ⟨j, rfl, hj, h⟩
  have eD : addr (s.gpr .edx) (bufOff w) = addr dA (bufOff w) + BitVec.ofNat 64 j := by
    rw [h.edx, MdStream.X86.addr_add_ofNat (by omega), addr_eq (by omega), BitVec.add_assoc,
      BitVec.ofNat_add, BitVec.add_comm (BitVec.ofNat 64 j)]
  have hout' : InRegions s.wr (addr dA (bufOff w) + BitVec.ofNat 64 j) 1 := by rw [h.wr]; exact hout j hj
  set m₁ := s.mem.writeW (addr dA (bufOff w) + BitVec.ofNat 64 j) ((s.gpr Reg8.al.reg).setWidth 8) with hm₁
  refine cons (s' := { s with mem := m₁ }) ?_ ?_
  · have e : s.ea (at_ .edx (VG.Impl.Blake2.X86.Stream.N w)) = addr dA (bufOff w) + BitVec.ofNat 64 j := eD
    simp only [exec, State.store8, e, hout', ite_true, hm₁]
  refine wp_addi fun s₂ u₂ => wp_subi fun s₃ u₃ _ hz₃ => WP.block_nil ?_
  have e₁ : ∀ r, ({ s with mem := m₁ } : State).gpr r = s.gpr r := fun _ => rfl
  have hcx' : s₃.gpr .ecx = BitVec.ofNat 32 (k - (j + 1)) := by
    rw [u₃.gpr, u₂.other _ (by decide), e₁, h.ecx, ofNat_pred (by omega), Nat.sub_sub]
  have hI : VG.Proof.Blake2.X86.Stream.Finalize.ZI (w := w) s₀ dA k (j + 1) s₃ := by
    refine ⟨by omega, ?_, hcx', fun x h1 h2 => ?_, ?_, ?_, ?_⟩
    · rw [u₃.other _ (by decide), u₂.gpr, e₁, h.edx, BitVec.add_assoc, BitVec.ofNat_add]; rfl
    · rw [u₃.other x h2, u₂.other x h1]; exact h.other x h1 h2
    · rw [u₃.rd, u₂.rd]; exact h.rd
    · rw [u₃.wr, u₂.wr]; exact h.wr
    · rw [u₃.mem, u₂.mem]
      show m₁ = _
      rw [hm₁, show Reg8.al.reg = Reg.eax from rfl, h.other .eax (by decide) (by decide), hax, h.mem,
        List.replicate_succ',
        VG.WriteBytes.writeBytes_snoc _ _ _ _ (by simp; omega), List.length_replicate]
      rfl
  have hzf : s₃.zf = some (decide (k - (j + 1) = 0)) := by
    rw [hz₃, u₂.other _ (by decide), e₁, h.ecx, ofNat_pred (show 1 ≤ k - j by omega), ofNat_beq_zero (by omega),
      show k - j - 1 = k - (j + 1) by omega]
  by_cases hjk : j + 1 = k
  · refine .inl ⟨?_, hQ _ (hjk ▸ hI)⟩
    simp only [VG.X86.eval, hzf, show k - (j + 1) = 0 by omega, decide_true, Option.map_some, Bool.not_true]
  · refine .inr ⟨?_, k - (j + 1), by omega, j + 1, rfl, by omega, hI⟩
    simp only [VG.X86.eval, hzf, show k - (j + 1) ≠ 0 by omega, decide_false, Option.map_some, Bool.not_false]

/-- Zeroing the buffer of the state at `ebx` (`st`) from byte `eax` (`r`) on. -/
theorem pad_ok (hP : VG.Proof.Blake2.X86.Stream.Ok P) {s : State} {st : BitVec 32} {r : Nat} (hr : r ≤ blockBytes w)
    (hfit : st.toNat + (bufOff w + blockBytes w) ≤ 2 ^ 32)
    (hbx : s.gpr .ebx = st) (hax : s.gpr .eax = BitVec.ofNat 32 r)
    (hdst : ∀ i < blockBytes w - r, InRegions s.wr (addr st (bufOff w + r) + BitVec.ofNat 64 i) 1) :
    WP isa (VG.Impl.Blake2.X86.Stream.pad w) s fun s' =>
      (∀ x, x ≠ .eax → x ≠ .ecx → x ≠ .edx → s'.gpr x = s.gpr x) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.mem = VG.WriteBytes.writeBytes s.mem (addr st (bufOff w + r)) (List.replicate (blockBytes w - r) 0) := by
  have hl := hP.len
  unfold VG.Impl.Blake2.X86.Stream.pad
  refine WP.seq (wp_mov fun s₁ u₁ => wp_add fun s₂ u₂ _ => wp_movi fun s₃ u₃ => wp_sub fun s₄ u₄ z₄ =>
    VG.Proof.Blake2.X86.Stream.wp_moviF fun s₅ u₅ _ zf₅ => WP.block_nil ?_)
  have g : ∀ x, x ≠ .eax → x ≠ .ecx → x ≠ .edx → s₅.gpr x = s.gpr x := fun x h1 h2 h3 => by
    rw [u₅.other x h1, u₄.other x h2, u₃.other x h2, u₂.other x h3, u₁.other x h3]
  have hcx : s₅.gpr .ecx = BitVec.ofNat 32 (blockBytes w - r) := by
    rw [u₅.other _ (by decide), u₄.gpr, u₃.gpr, u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), hax, VG.Proof.Blake2.X86.Stream.B_eq, sub_ofNat hr]
  have hdx : s₅.gpr .edx = st + BitVec.ofNat 32 r := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.gpr,
      u₁.other _ (by decide), hbx, hax]
  have hz : isa.eval .e s₅ = some (decide (blockBytes w - r = 0)) := by
    show s₅.zf = _
    rw [zf₅, z₄, ← u₄.gpr, ← u₅.other .ecx (by decide), hcx, ofNat_beq_zero (by omega)]
  have hm₅ : s₅.mem = s.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have hwr : s₅.wr = s.wr := by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  have hrd : s₅.rd = s.rd := by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  refine WP.ite _ hz (fun hb => WP.block_nil ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    refine ⟨g, hrd, hwr, ?_⟩
    rw [hb, List.replicate_zero, VG.WriteBytes.writeBytes_nil, hm₅]
  · simp only [decide_eq_false_iff_not] at hb
    have e : addr (st + BitVec.ofNat 32 r) (bufOff w) = addr st (bufOff w + r) := by
      rw [MdStream.X86.addr_add_ofNat (by omega), addr_eq (by omega), Nat.add_comm]
    refine VG.Proof.Blake2.X86.Stream.Finalize.zeroLoop_ok (w := w) (dA := st + BitVec.ofNat 32 r) (by omega) (by omega)
      (by rw [VG.Proof.Blake2.X86.Stream.toNat_add_ofNat (by omega)]; omega) hdx hcx u₅.gpr
      (fun i hi => by rw [hwr, e]; exact hdst i hi) fun s' h => ?_
    refine ⟨fun x h1 h2 h3 => by rw [h.other x h3 h2, g x h1 h2 h3], by rw [h.rd, hrd], by rw [h.wr, hwr], ?_⟩
    rw [h.mem, hm₅, e]

/-! ## Bytes -/

theorem writeW_eq (m : Mem) (a : Addr) (v : BitVec 32) : m.writeW a v = VG.WriteBytes.writeBytes m a (VG.Spec.Blake2.wordBytes v) := by
  rw [Mem.writeW, VG.WriteBytes.write_eq_writeBytes]; rfl

theorem writeBytes_at (m : Mem) (q : Addr) (xs : List Byte) {i : Nat} (hi : i < 2 ^ 64) :
    VG.WriteBytes.writeBytes m q xs (q + BitVec.ofNat 64 i) = if i < xs.length then xs.getD i 0 else m (q + BitVec.ofNat 64 i) := by
  simp only [VG.WriteBytes.writeBytes]
  rw [show q + BitVec.ofNat 64 i - q = BitVec.ofNat 64 i by rw [BitVec.add_comm]; exact BitVec.add_sub_cancel _ _,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi]

theorem bytesAt_writeBytes_self (m : Mem) (q : Addr) {xs : List Byte} {n : Nat} (hn : xs.length = n)
    (h : n < 2 ^ 64) : VG.Spec.Blake2.bytesAt (VG.WriteBytes.writeBytes m q xs) q n = xs := by
  subst hn
  apply List.ext_getElem (by simp [VG.Spec.Blake2.bytesAt])
  intro i h1 _
  simp only [VG.Spec.Blake2.bytesAt, List.length_map, List.length_range] at h1
  simp only [VG.Spec.Blake2.bytesAt, List.getElem_map, List.getElem_range, VG.Proof.Blake2.X86.Stream.Finalize.writeBytes_at m q xs (by omega : i < 2 ^ 64),
    h1, ↓reduceIte, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1, Option.getD_some]

/-- The buffer after zeroing it from byte `r` on. -/
theorem pad_bytes {m m' : Mem} {st : Addr} {N r bb : Nat} (hr : r ≤ bb) (hlt : N + bb < 2 ^ 64)
    (hm : m' = VG.WriteBytes.writeBytes m (st + BitVec.ofNat 64 (N + r)) (List.replicate (bb - r) 0)) :
    VG.Spec.Blake2.bytesAt m' (st + BitVec.ofNat 64 N) bb =
      VG.Spec.Blake2.bytesAt m (st + BitVec.ofNat 64 N) r ++ List.replicate (bb - r) 0 := by
  conv_lhs => rw [show bb = r + (bb - r) by omega]
  rw [bytesAt_add, Offset.add_ofNat_add_ofNat]
  congr 1
  · refine bytesAt_congr fun i hi => ?_
    rw [hm, Offset.add_ofNat_add_ofNat,
      VG.WriteBytes.writeBytes_before m st _ (by omega : N + i < N + r) (by simp; omega)]
  · rw [hm]; exact VG.Proof.Blake2.X86.Stream.Finalize.bytesAt_writeBytes_self _ _ (by simp) (by omega)

/-! ## Copying the hash value out -/

/-- After copying `k` words. -/
def OInv (σ : State) (k : Nat) (s : State) : Prop :=
  (∀ r, r ≠ .ecx → s.gpr r = σ.gpr r) ∧ s.rd = σ.rd ∧ s.wr = σ.wr ∧
    s.mem = VG.WriteBytes.writeBytes σ.mem ((σ.gpr .eax).setWidth 64) (VG.Spec.Blake2.bytesAt σ.mem ((σ.gpr .ebx).setWidth 64) (4 * k))

theorem output_ok {σ : State} (hN4 : bufOff w % 4 = 0)
    (hfs : (σ.gpr .ebx).toNat + bufOff w ≤ 2 ^ 32) (hfo : (σ.gpr .eax).toNat + bufOff w ≤ 2 ^ 32)
    (hin : ∀ a n, (⟨(σ.gpr .ebx).setWidth 64, bufOff w⟩ : Region).Contains a n → InRegions (σ.rd ++ σ.wr) a n)
    (hout : ∀ a n, (⟨(σ.gpr .eax).setWidth 64, bufOff w⟩ : Region).Contains a n → InRegions σ.wr a n)
    (hd : Region.Disjoint ⟨(σ.gpr .ebx).setWidth 64, bufOff w⟩ ⟨(σ.gpr .eax).setWidth 64, bufOff w⟩) :
    WP isa (.block (output w)) σ fun s =>
      (∀ r, r ≠ .ecx → s.gpr r = σ.gpr r) ∧ s.rd = σ.rd ∧ s.wr = σ.wr ∧
      s.mem = VG.WriteBytes.writeBytes σ.mem ((σ.gpr .eax).setWidth 64)
        (VG.Spec.Blake2.bytesAt σ.mem ((σ.gpr .ebx).setWidth 64) (bufOff w)) := by
  have e : 4 * (Impl.Blake2.X86.Stream.N w / 4) = bufOff w := by rw [VG.Proof.Blake2.X86.Stream.N_eq]; omega
  unfold output
  rw [← e]
  refine wp_range_flatMap (M := isa) (VG.Proof.Blake2.X86.Stream.Finalize.OInv σ) (fun k s hk ⟨hg, hrd, hwr, hm⟩ => ?_) _ (Nat.le_refl _) σ
    ⟨fun _ _ => rfl, rfl, rfl, by rw [Nat.mul_zero]; simp [VG.Spec.Blake2.bytesAt, VG.WriteBytes.writeBytes_nil]⟩
  rw [VG.Proof.Blake2.X86.Stream.N_eq] at hk
  have hk4 : 4 * k + 4 ≤ bufOff w := by omega
  have hl : (VG.Spec.Blake2.bytesAt σ.mem ((σ.gpr .ebx).setWidth 64) (4 * k)).length = 4 * k := by simp [VG.Spec.Blake2.bytesAt]
  have eS : addr (σ.gpr .ebx) (4 * k) = (σ.gpr .ebx).setWidth 64 + BitVec.ofNat 64 (4 * k) := addr_eq (by omega)
  have eO : addr (σ.gpr .eax) (4 * k) = (σ.gpr .eax).setWidth 64 + BitVec.ofNat 64 (4 * k) := addr_eq (by omega)
  refine wp_ldm (B := σ.gpr .ebx) (by rw [hg _ (by decide)])
    (by rw [hrd, hwr, eS]; exact hin _ _ (Offset.contains_base _ hk4 (by omega))) fun s₁ u₁ => ?_
  refine wp_stm (B := σ.gpr .eax) (by rw [u₁.other _ (by decide), hg _ (by decide)])
    (by rw [u₁.wr, hwr, eO]; exact hout _ _ (Offset.contains_base _ hk4 (by omega))) fun s₂ u₂ =>
      WP.block_nil ⟨fun r hr => by rw [u₂.gpr, u₁.other r hr, hg r hr], by rw [u₂.rd, u₁.rd, hrd],
        by rw [u₂.wr, u₁.wr, hwr], ?_⟩
  have hv : s.mem.readW (addr (σ.gpr .ebx) (4 * k)) 32 = σ.mem.readW (addr (σ.gpr .ebx) (4 * k)) 32 := by
    rw [hm, eS]
    exact (VG.WriteBytes.writeBytes_frame (R := ⟨(σ.gpr .eax).setWidth 64, bufOff w⟩) _ _ _
      (VG.Proof.Blake2.X86.Stream.contains_prefix _ (by omega))).readW
      (Offset.contains_base (k := bufOff w) _ hk4 (by omega)) (by simpa using hd) (by decide)
  have e' := VG.WriteBytes.writeBytes_append σ.mem ((σ.gpr .eax).setWidth 64) (VG.Spec.Blake2.bytesAt σ.mem ((σ.gpr .ebx).setWidth 64) (4 * k))
    (VG.Spec.Blake2.wordBytes (σ.mem.readW ((σ.gpr .ebx).setWidth 64 + BitVec.ofNat 64 (4 * k)) 32))
    (by rw [hl]; simp [VG.Spec.Blake2.wordBytes]; omega)
  rw [hl] at e'
  rw [u₂.mem, u₁.gpr, u₁.mem, hv, hm, eO, eS, VG.Proof.Blake2.X86.Stream.Finalize.writeW_eq, e', wordBytes_readW _ _ (.inl rfl),
    ← bytesAt_add, Nat.mul_succ]

/-! ## The epilogue -/

theorem restore_ok {s₀ : State} (hp : VG.Proof.Blake2.X86.Stream.Finalize.Pre w s₀) {s : State} (hbp : s.gpr .ebp = VG.Proof.Blake2.X86.Stream.Finalize.scr s₀)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (hsv : VG.Proof.Blake2.X86.Stream.Saved (VG.Proof.Blake2.X86.Stream.Finalize.scr s₀) s₀ s.mem) :
    WP isa (.block restore) s fun s' =>
      (∀ r ∈ calleeSaved, r ≠ .esp → s'.gpr r = s₀.gpr r) ∧ s'.gpr .esp = s.gpr .esp ∧ s'.mem = s.mem :=
  VG.Proof.Blake2.X86.Stream.restore_saved hbp (fun d _ hd => hp.sinr hrd hwr (by omega)) hsv

/-! ## The whole function -/

theorem compressBlocks_one (h : VG.Spec.Blake2.HashValue w) (m : Mem) (p : Addr) (t : Nat) (f : Bool) :
    VG.Spec.Blake2.compressBlocks P h m p 1 t f = F P h (VG.Spec.Blake2.blockAt w m p) t f := by
  rw [show (1 : Nat) = 0 + 1 from rfl, compressBlocks_succ, compressBlocks_zero]; simp

/-- The arguments are kept by writes to the writable buffers and below the
stack. -/
theorem arg_keep {s₀ : State} (hp : VG.Proof.Blake2.X86.Stream.Finalize.Pre w s₀) {m : Mem}
    (hf : Frame [VG.Proof.Blake2.X86.Stream.Finalize.stR s₀ w, VG.Proof.Blake2.X86.Stream.Finalize.outR s₀ w, VG.Proof.Blake2.X86.Stream.Finalize.scR s₀, VG.Proof.Blake2.X86.Stream.Finalize.stkR s₀] s₀.mem m) {d : Nat} (h₁ : 4 ≤ d) (h₂ : d + 4 ≤ 24) :
    m.readW (addr (VG.Proof.Blake2.X86.Stream.Finalize.esp₀ s₀) d) 32 = s₀.mem.readW (addr (VG.Proof.Blake2.X86.Stream.Finalize.esp₀ s₀) d) 32 := by
  refine hf.readW (r := ⟨addr (VG.Proof.Blake2.X86.Stream.Finalize.esp₀ s₀) d, 4⟩) (Region.contains_self _ _) ?_ (by decide)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hp.a_st.sub_left (hp.arg_sub h₁ h₂)
  · exact hp.a_out.sub_left (hp.arg_sub h₁ h₂)
  · exact hp.a_scr.sub_left (hp.arg_sub h₁ h₂)
  · exact hp.a_stk.sub_left (hp.arg_sub h₁ h₂)

theorem correct (hP : VG.Proof.Blake2.X86.Stream.Ok P) {name : String} {code : Prog isa} (hf : VG.Proof.Blake2.X86.Stream.CalleeOk P code) {s₀ : State}
    (hp : VG.Proof.Blake2.X86.Stream.Finalize.Pre w s₀) :
    WP isa (finalize w name code) s₀ fun s' => abiPreserved s₀ s' ∧ (finalizeX86 P).post s₀ s' := by
  have hl := hP.len
  have hpos := hP.pos
  have hN := hP.N
  have fS := hp.st_fit; have fO := hp.out_fit; have fC := hp.scr_fit
  have hstN : Region.Sub ⟨VG.Proof.Blake2.X86.Stream.Finalize.stA s₀, bufOff w⟩ (VG.Proof.Blake2.X86.Stream.Finalize.stR s₀ w) := Region.sub_prefix (by omega)
  have hsc : Region.Sub ⟨VG.Proof.Blake2.X86.Stream.Finalize.scA s₀, 512⟩ (VG.Proof.Blake2.X86.Stream.Finalize.scR s₀) := Region.sub_prefix (by omega)
  have eB : (VG.Proof.Blake2.X86.Stream.Finalize.st s₀ + BitVec.ofNat 32 (bufOff w)).setWidth 64 = VG.Proof.Blake2.X86.Stream.Finalize.stA s₀ + BitVec.ofNat 64 (bufOff w) :=
    VG.Proof.Blake2.X86.Stream.sw_add (by omega)
  have hbuf : Region.Sub ⟨VG.Proof.Blake2.X86.Stream.Finalize.stA s₀ + BitVec.ofNat 64 (bufOff w), blockBytes w⟩ (VG.Proof.Blake2.X86.Stream.Finalize.stR s₀ w) :=
    Offset.sub_base _ (by omega)
  unfold finalize
  refine WP.seq (WP.mono (VG.Proof.Blake2.X86.Stream.Finalize.prologue_ok hp) fun s₁ h₁ => ?_)
  have F₁ : Frame [VG.Proof.Blake2.X86.Stream.Finalize.scR s₀] s₀.mem s₁.mem := by rw [h₁.mem]; exact VG.Proof.Blake2.X86.Stream.saveMem_frame hp.scr_fit s₀
  refine WP.seq (WP.mono (VG.Proof.Blake2.X86.Stream.Finalize.bufLen_val hP h₁.eax h₁.ecx) fun s₂ ⟨ax₂, g₂, m₂, rd₂, wr₂⟩ => ?_)
  generalize hr : Proof.Blake2.bufLen w (VG.X86.arg s₀ 2 ++ VG.X86.arg s₀ 1).toNat = r at ax₂
  have hrB : r ≤ blockBytes w := hr ▸ bufLen_le hpos _
  have bx₂ : s₂.gpr .ebx = VG.Proof.Blake2.X86.Stream.Finalize.st s₀ := by rw [g₂ _ (by decide) (by decide), h₁.ebx]
  have eP : r < blockBytes w → addr (VG.Proof.Blake2.X86.Stream.Finalize.st s₀) (bufOff w + r) = VG.Proof.Blake2.X86.Stream.Finalize.stA s₀ + BitVec.ofNat 64 (bufOff w + r) :=
    fun h => addr_eq (by omega)
  refine WP.seq (WP.mono (VG.Proof.Blake2.X86.Stream.Finalize.pad_ok hP hrB fS bx₂ ax₂ fun i hi => ?_) fun s₃ ⟨g₃, rd₃, wr₃, m₃⟩ => ?_)
  · rw [wr₂, h₁.wr, hp.wr, eP (by omega), Offset.add_add]
    exact ⟨VG.Proof.Blake2.X86.Stream.Finalize.stR s₀ w, by simp, contains_offset (by omega) (by omega)⟩
  have hm₃ : s₃.mem = VG.WriteBytes.writeBytes s₁.mem (VG.Proof.Blake2.X86.Stream.Finalize.stA s₀ + BitVec.ofNat 64 (bufOff w + r))
      (List.replicate (blockBytes w - r) 0) := by
    rw [m₃, m₂]
    by_cases h : r < blockBytes w
    · rw [eP h]
    · rw [show blockBytes w - r = 0 by omega, List.replicate_zero, VG.WriteBytes.writeBytes_nil, VG.WriteBytes.writeBytes_nil]
  have F₃ : Frame [VG.Proof.Blake2.X86.Stream.Finalize.stR s₀ w] s₁.mem s₃.mem := by
    rw [hm₃]; exact VG.WriteBytes.writeBytes_frame _ _ _ (contains_offset (by simp; omega) (by omega))
  have F₀₃ : Frame [VG.Proof.Blake2.X86.Stream.Finalize.stR s₀ w, VG.Proof.Blake2.X86.Stream.Finalize.outR s₀ w, VG.Proof.Blake2.X86.Stream.Finalize.scR s₀, VG.Proof.Blake2.X86.Stream.Finalize.stkR s₀] s₀.mem s₃.mem :=
    (F₁.mono (by simp)).trans (F₃.mono (by simp))
  have g₃' : ∀ x, x ≠ .eax → x ≠ .ecx → x ≠ .edx → s₃.gpr x = s₁.gpr x := fun x h1 h2 h3 => by
    rw [g₃ x h1 h2 h3, g₂ x h1 h2]
  have rd₃' : s₃.rd = s₀.rd := by rw [rd₃, rd₂, h₁.rd]
  have wr₃' : s₃.wr = s₀.wr := by rw [wr₃, wr₂, h₁.wr]
  have sp₃ : s₃.gpr .esp = VG.Proof.Blake2.X86.Stream.Finalize.esp₀ s₀ := by rw [g₃' _ (by decide) (by decide) (by decide), h₁.esp]
  -- The call.
  refine WP.seq ?_
  unfold compressLast
  refine WP.seq (wp_mov fun s₄ u₄ => wp_addi fun s₅ u₅ => wp_movi fun s₆ u₆ => wp_movi fun s₇ u₇ => ?_)
  have g₇ : ∀ x, x ≠ .esi → x ≠ .edi → x ≠ .eax → s₇.gpr x = s₃.gpr x := fun x h1 h2 h3 => by
    rw [u₇.other x h3, u₆.other x h2, u₅.other x h1, u₄.other x h1]
  have m₇ : s₇.mem = s₃.mem := by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem]
  have rd₇ : s₇.rd = s₀.rd := by rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, rd₃']
  have wr₇ : s₇.wr = s₀.wr := by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, wr₃']
  have sp₇ : s₇.gpr .esp = VG.Proof.Blake2.X86.Stream.Finalize.esp₀ s₀ := by rw [g₇ _ (by decide) (by decide) (by decide), sp₃]
  refine wp_ldm sp₇ (hp.rin rd₇ (d := 8) (by omega) (by omega)) fun s₈ u₈ => ?_
  have i12 := hp.rin rd₇ (d := 12) (by omega) (by omega)
  refine wp_ldm (by rw [u₈.other _ (by decide), sp₇]) (by rw [u₈.rd, u₈.wr]; exact i12) fun s₉ u₉ => WP.block_nil ?_
  have g₉ : ∀ x, x ≠ .esi → x ≠ .edi → x ≠ .eax → x ≠ .ecx → x ≠ .edx → s₉.gpr x = s₁.gpr x :=
    fun x h1 h2 h3 h4 h5 => by rw [u₉.other x h5, u₈.other x h4, g₇ x h1 h2 h3, g₃' x h3 h4 h5]
  have m₉ : s₉.mem = s₃.mem := by rw [u₉.mem, u₈.mem, m₇]
  have rd₉ : s₉.rd = s₀.rd := by rw [u₉.rd, u₈.rd, rd₇]
  have wr₉ : s₉.wr = s₀.wr := by rw [u₉.wr, u₈.wr, wr₇]
  have cx₉ : s₉.gpr .ecx = VG.X86.arg s₀ 1 := by
    rw [u₉.other _ (by decide), u₈.gpr, m₇, VG.Proof.Blake2.X86.Stream.Finalize.arg_keep hp F₀₃ (by omega) (by omega)]; rfl
  have dx₉ : s₉.gpr .edx = VG.X86.arg s₀ 2 := by
    rw [u₉.gpr, u₈.mem, m₇, VG.Proof.Blake2.X86.Stream.Finalize.arg_keep hp F₀₃ (by omega) (by omega)]; rfl
  have esp₉ : s₉.gpr .esp = VG.Proof.Blake2.X86.Stream.Finalize.esp₀ s₀ := by
    rw [g₉ _ (by decide) (by decide) (by decide) (by decide) (by decide), h₁.esp]
  refine VG.Proof.Blake2.X86.Stream.call_ok (P := P) hf (k := 1) esp₉
    (by rw [g₉ _ (by decide) (by decide) (by decide) (by decide) (by decide), h₁.ebx])
    (by rw [g₉ _ (by decide) (by decide) (by decide) (by decide) (by decide), h₁.ebp])
    (by rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
      u₅.gpr, u₄.gpr, g₃' _ (by decide) (by decide) (by decide), h₁.ebx, VG.Proof.Blake2.X86.Stream.N_eq])
    (by rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr]; rfl)
    cx₉ dx₉ (by rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr]) hp.sp_lo (by omega)
    (by rw [VG.Proof.Blake2.X86.Stream.toNat_add_ofNat (by omega)]; omega) (by omega)
    ((hp.st_scr.sub_left hstN).sub_right hsc) (by rw [eB]; exact Offset.disjoint_base _ (Nat.le_refl _) (by omega))
    (by rw [eB, Nat.mul_one]; exact (hp.st_scr.sub_left hbuf).sub_right hsc) (hp.stk_st.sub_right hstN)
    (hp.stk_scr.sub_right hsc) (by rw [eB, Nat.mul_one]; exact hp.stk_st.sub_right hbuf) ?_ ?_ fun s₁₀ rd₁₀ wr₁₀ cs₁₀ f₁₀ e₁₀ => ?_
  · rw [rd₉, wr₉, hp.rd, hp.wr]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨VG.Proof.Blake2.X86.Stream.Finalize.stR s₀ w, by simp, bufOff w, by rw [eB], by simp only; omega⟩
  · rw [wr₉, hp.wr]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨VG.Proof.Blake2.X86.Stream.Finalize.stR s₀ w, by simp, 0, by simp, by simp only; omega⟩
    · exact ⟨VG.Proof.Blake2.X86.Stream.Finalize.scR s₀, by simp, 0, by simp, by simp only; omega⟩
  have sp₁₀ : s₁₀.gpr .esp = VG.Proof.Blake2.X86.Stream.Finalize.esp₀ s₀ := by rw [cs₁₀ _ (by decide), esp₉]
  have bx₁₀ : s₁₀.gpr .ebx = VG.Proof.Blake2.X86.Stream.Finalize.st s₀ := by
    rw [cs₁₀ _ (by decide), g₉ _ (by decide) (by decide) (by decide) (by decide) (by decide), h₁.ebx]
  have bp₁₀ : s₁₀.gpr .ebp = VG.Proof.Blake2.X86.Stream.Finalize.scr s₀ := by
    rw [cs₁₀ _ (by decide), g₉ _ (by decide) (by decide) (by decide) (by decide) (by decide), h₁.ebp]
  have rd₁₀' : s₁₀.rd = s₀.rd := rd₁₀.trans rd₉
  have wr₁₀' : s₁₀.wr = s₀.wr := wr₁₀.trans wr₉
  have F₃₁₀ : Frame [VG.Proof.Blake2.X86.Stream.Finalize.stR s₀ w, VG.Proof.Blake2.X86.Stream.Finalize.outR s₀ w, VG.Proof.Blake2.X86.Stream.Finalize.scR s₀, VG.Proof.Blake2.X86.Stream.Finalize.stkR s₀] s₃.mem s₁₀.mem := by
    rw [← m₉]
    refine f₁₀.sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨VG.Proof.Blake2.X86.Stream.Finalize.stR s₀ w, by simp, hstN⟩
    · exact ⟨VG.Proof.Blake2.X86.Stream.Finalize.scR s₀, by simp, hsc⟩
    · exact ⟨VG.Proof.Blake2.X86.Stream.Finalize.stkR s₀, by simp, fun _ h => h⟩
  have F₀₁₀ := F₀₃.trans F₃₁₀
  refine wp_ldm sp₁₀ (hp.rin rd₁₀' (d := 16) (by omega) (by omega)) fun s₁₁ u₁₁ => ?_
  have ax₁₁ : s₁₁.gpr .eax = VG.Proof.Blake2.X86.Stream.Finalize.op s₀ := by rw [u₁₁.gpr, VG.Proof.Blake2.X86.Stream.Finalize.arg_keep hp F₀₁₀ (by omega) (by omega)]; rfl
  have bx₁₁ : s₁₁.gpr .ebx = VG.Proof.Blake2.X86.Stream.Finalize.st s₀ := by rw [u₁₁.other _ (by decide), bx₁₀]
  rw [show (output w).append restore = output w ++ restore from rfl, WP.block_append_iff]
  have hN4 : bufOff w % 4 = 0 := by rcases hP.bb with h | h <;> omega
  refine WP.mono (VG.Proof.Blake2.X86.Stream.Finalize.output_ok (σ := s₁₁) hN4 (by rw [bx₁₁]; omega) (by rw [ax₁₁]; omega)
    (fun a n h => ?_) (fun a n h => ?_) (by rw [bx₁₁, ax₁₁]; exact hp.st_out.sub_left hstN))
    fun s₁₂ ⟨g₁₂, rd₁₂, wr₁₂, m₁₂⟩ => ?_
  · rw [u₁₁.rd, u₁₁.wr, rd₁₀', wr₁₀', hp.rd, hp.wr]
    rw [bx₁₁] at h
    exact ⟨VG.Proof.Blake2.X86.Stream.Finalize.stR s₀ w, by simp, by simp only [Region.Contains, VG.Proof.Blake2.X86.Stream.Finalize.stA] at h ⊢; omega⟩
  · rw [u₁₁.wr, wr₁₀', hp.wr]
    rw [ax₁₁] at h
    exact ⟨VG.Proof.Blake2.X86.Stream.Finalize.outR s₀ w, by simp, h⟩
  have F₁₂ : Frame [VG.Proof.Blake2.X86.Stream.Finalize.outR s₀ w] s₁₁.mem s₁₂.mem := by
    rw [m₁₂, ax₁₁]
    exact VG.WriteBytes.writeBytes_frame _ _ _ (VG.Proof.Blake2.X86.Stream.contains_prefix _ (by simp [VG.Spec.Blake2.bytesAt]))
  -- The saved registers.
  have sv₁ : VG.Proof.Blake2.X86.Stream.Saved (VG.Proof.Blake2.X86.Stream.Finalize.scr s₀) s₀ s₁.mem := by rw [h₁.mem]; exact VG.Proof.Blake2.X86.Stream.saveMem_saved hp.scr_fit s₀
  have sv₃ : VG.Proof.Blake2.X86.Stream.Saved (VG.Proof.Blake2.X86.Stream.Finalize.scr s₀) s₀ s₃.mem :=
    Saved.keep hp.scr_fit sv₁ (F₃.mono fun r hr => List.mem_cons_of_mem _ hr) (by simpa using hp.st_scr.symm)
  have f₁₀' : Frame [⟨VG.Proof.Blake2.X86.Stream.Finalize.scA s₀, 512⟩, ⟨VG.Proof.Blake2.X86.Stream.Finalize.stA s₀, bufOff w⟩, VG.Proof.Blake2.X86.Stream.Finalize.stkR s₀] s₉.mem s₁₀.mem :=
    f₁₀.mono fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp
  have sv₁₀ : VG.Proof.Blake2.X86.Stream.Saved (VG.Proof.Blake2.X86.Stream.Finalize.scr s₀) s₀ s₁₀.mem :=
    Saved.keep hp.scr_fit (by rw [m₉]; exact sv₃) f₁₀' (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨(hp.st_scr.sub_left hstN).symm, hp.stk_scr.symm⟩)
  have sv₁₂ : VG.Proof.Blake2.X86.Stream.Saved (VG.Proof.Blake2.X86.Stream.Finalize.scr s₀) s₀ s₁₂.mem :=
    Saved.keep hp.scr_fit (by rw [← u₁₁.mem] at sv₁₀; exact sv₁₀) (F₁₂.mono fun r hr => List.mem_cons_of_mem _ hr)
      (by simpa using hp.out_scr.symm)
  have bp₁₂ : s₁₂.gpr .ebp = VG.Proof.Blake2.X86.Stream.Finalize.scr s₀ := by rw [g₁₂ _ (by decide), u₁₁.other _ (by decide), bp₁₀]
  refine WP.mono (VG.Proof.Blake2.X86.Stream.Finalize.restore_ok hp bp₁₂ (by rw [rd₁₂, u₁₁.rd, rd₁₀']) (by rw [wr₁₂, u₁₁.wr, wr₁₀']) sv₁₂)
    fun s₁₃ ⟨cs₁₃, sp₁₃, m₁₃⟩ => ?_
  have F₀₁₂ : Frame [VG.Proof.Blake2.X86.Stream.Finalize.stR s₀ w, VG.Proof.Blake2.X86.Stream.Finalize.outR s₀ w, VG.Proof.Blake2.X86.Stream.Finalize.scR s₀, VG.Proof.Blake2.X86.Stream.Finalize.stkR s₀] s₀.mem s₁₂.mem :=
    F₀₁₀.trans (by rw [← u₁₁.mem]; exact F₁₂.mono (by simp))
  refine ⟨⟨fun r hr => ?_, ?_⟩, fun h0 d hR hlt hcnt => ?_⟩
  · by_cases h : r = .esp
    · subst h
      rw [sp₁₃, g₁₂ _ (by decide), u₁₁.other _ (by decide), sp₁₀]
    · exact cs₁₃ r hr h
  · rw [m₁₃]
    exact F₀₁₂.readW (Region.contains_self _ _)
      (by simpa using ⟨hp.ret_st, hp.ret_out, hp.ret_scr, hp.ret_stk⟩) (by decide)
  · have hn : (VG.X86.arg s₀ 2 ++ VG.X86.arg s₀ 1).toNat = d.length := by
      show (countX86 s₀).toNat = _
      rw [hcnt, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
    rw [hn] at hr
    subst hr
    have hst : ∀ i < bufOff w + blockBytes w,
        s₁.mem (VG.Proof.Blake2.X86.Stream.Finalize.stA s₀ + BitVec.ofNat 64 i) = s₀.mem (VG.Proof.Blake2.X86.Stream.Finalize.stA s₀ + BitVec.ofNat 64 i) :=
      fun i hi => F₁.bytes (R := VG.Proof.Blake2.X86.Stream.Finalize.stR s₀ w) (by simpa using hp.st_scr) (by simp only; omega) hi
    show VG.Spec.Blake2.bytesAt s₁₃.mem (VG.Proof.Blake2.X86.Stream.Finalize.opA s₀) (bufOff w) = _
    rw [m₁₃, m₁₂, ax₁₁, bx₁₁, VG.Proof.Blake2.X86.Stream.Finalize.bytesAt_writeBytes_self _ _ (by simp [VG.Spec.Blake2.bytesAt]) (by omega), u₁₁.mem,
      bytesAt_state _ _ (by rcases hP.w with h | h <;> simp [h]), e₁₀,
      show ((1 : BitVec 32) != 0) = true from rfl, VG.Proof.Blake2.X86.Stream.Finalize.compressBlocks_one, hn, eB, m₉]
    refine final_eq P hpos hR ?_ ?_
    · exact stateAt_congr fun i hi => by
        rw [hm₃, VG.WriteBytes.writeBytes_before s₁.mem _ _ (by omega : i < bufOff w + Proof.Blake2.bufLen w d.length)
          (by simp; omega), hst i (by omega)]
    · rw [VG.Proof.Blake2.X86.Stream.Finalize.pad_bytes hrB (by omega) hm₃]
      congr 1
      exact bytesAt_congr fun i hi => by rw [Offset.add_ofNat_add_ofNat, hst _ (by omega)]

end VG.Proof.Blake2.X86.Stream.Finalize

end

/- Proofs formerly in `VerifiedGarbage.Proof.Blake2.X86.Stream.Init`. -/
section

/-!
# Streaming BLAKE2 on x86 (32-bit): `init`

`init` copies the key, if any, into the zeroed buffer (`keyBlock_ok`), keeping
our caller's `ebx` in the first word of the hash value meanwhile, then stores
the initial hash value (`initState_ok`), for either word size.
-/

namespace VG.Proof.Blake2.X86.Stream.Init

open VG VG.X86 VG.X86.Wp VG.Spec.Blake2
open VG.Impl.Blake2.X86 (at_)
open VG.Impl.Blake2.X86.Stream
open VG.Proof.Blake2 (initX86 repr_keyBlock stateAt_congr bytesAt_congr bytesAt_add)
open VG.WriteBytes (writeBytes writeBytes_nil writeBytes_snoc writeBytes_frame writeBytes_append
  writeBytes_before write_eq_writeBytes)
open VG.Proof.MdStream.X86 (contains_addr sub_offset contains_offset)

variable {w : Nat} {P : VG.Spec.Blake2.Params w}

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev esp₀ : BitVec 32 := s₀.gpr .esp
abbrev st : BitVec 32 := VG.X86.arg s₀ 0
abbrev nn : Nat := (VG.X86.arg s₀ 1).toNat
abbrev key : BitVec 32 := VG.X86.arg s₀ 2
abbrev kk : Nat := (VG.X86.arg s₀ 3).toNat
abbrev stA : Addr := (VG.Proof.Blake2.X86.Stream.Init.st s₀).setWidth 64
abbrev keyA : Addr := (VG.Proof.Blake2.X86.Stream.Init.key s₀).setWidth 64
abbrev stR (w : Nat) : Region := ⟨VG.Proof.Blake2.X86.Stream.Init.stA s₀, bufOff w + blockBytes w⟩
abbrev keyR : Region := ⟨VG.Proof.Blake2.X86.Stream.Init.keyA s₀, VG.Proof.Blake2.X86.Stream.Init.kk s₀⟩
abbrev argR : Region := ⟨argAddr s₀ 0, 16⟩
abbrev retR : Region := ⟨(VG.Proof.Blake2.X86.Stream.Init.esp₀ s₀).setWidth 64, 4⟩
/-- The key. -/
abbrev K : List Byte := bytesAt s₀.mem (VG.Proof.Blake2.X86.Stream.Init.keyA s₀) (VG.Proof.Blake2.X86.Stream.Init.kk s₀)

end

structure Pre (P : VG.Spec.Blake2.Params w) (s₀ : State) : Prop where
  rd : s₀.rd = [VG.Proof.Blake2.X86.Stream.Init.keyR s₀, VG.Proof.Blake2.X86.Stream.Init.argR s₀]
  wr : s₀.wr = [VG.Proof.Blake2.X86.Stream.Init.stR s₀ w]
  key_st : (VG.Proof.Blake2.X86.Stream.Init.keyR s₀).Disjoint (VG.Proof.Blake2.X86.Stream.Init.stR s₀ w)
  a_st : (VG.Proof.Blake2.X86.Stream.Init.argR s₀).Disjoint (VG.Proof.Blake2.X86.Stream.Init.stR s₀ w)
  ret_st : (VG.Proof.Blake2.X86.Stream.Init.retR s₀).Disjoint (VG.Proof.Blake2.X86.Stream.Init.stR s₀ w)
  st_fit : (VG.Proof.Blake2.X86.Stream.Init.st s₀).toNat + (bufOff w + blockBytes w) ≤ 2 ^ 32
  key_fit : (VG.Proof.Blake2.X86.Stream.Init.key s₀).toNat + VG.Proof.Blake2.X86.Stream.Init.kk s₀ ≤ 2 ^ 32
  sp_fit : (VG.Proof.Blake2.X86.Stream.Init.esp₀ s₀).toNat + 20 ≤ 2 ^ 32
  nn_lo : 1 ≤ VG.Proof.Blake2.X86.Stream.Init.nn s₀
  nn_hi : VG.Proof.Blake2.X86.Stream.Init.nn s₀ ≤ P.maxBytes
  kk_hi : VG.Proof.Blake2.X86.Stream.Init.kk s₀ ≤ P.maxBytes

theorem pre_of {s₀ : State} (h : (initX86 P).pre s₀) : VG.Proof.Blake2.X86.Stream.Init.Pre P s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

namespace Pre
variable {s₀ : State} (hp : VG.Proof.Blake2.X86.Stream.Init.Pre P s₀)
include hp

theorem arg_in {d : Nat} (hd₁ : 4 ≤ d) (hd : d + 4 ≤ 20) : (VG.Proof.Blake2.X86.Stream.Init.argR s₀).Contains (addr (VG.Proof.Blake2.X86.Stream.Init.esp₀ s₀) d) 4 := by
  have := hp.sp_fit
  show (⟨addr (VG.Proof.Blake2.X86.Stream.Init.esp₀ s₀) 4, 16⟩ : Region).Contains _ _
  rw [addr_eq (by omega), addr_eq (by omega)]
  exact Offset.contains _ hd₁ (by omega) (by omega)

theorem arg_sub {d : Nat} (hd₁ : 4 ≤ d) (hd : d + 4 ≤ 20) : Region.Sub ⟨addr (VG.Proof.Blake2.X86.Stream.Init.esp₀ s₀) d, 4⟩ (VG.Proof.Blake2.X86.Stream.Init.argR s₀) := by
  have := hp.sp_fit
  show Region.Sub _ ⟨addr (VG.Proof.Blake2.X86.Stream.Init.esp₀ s₀) 4, 16⟩
  rw [addr_eq (by omega), addr_eq (by omega)]
  exact Offset.sub _ hd₁ (by omega)

theorem rin {s : State} (hrd : s.rd = s₀.rd) {d : Nat} (h₁ : 4 ≤ d) (h₂ : d + 4 ≤ 20) :
    InRegions (s.rd ++ s.wr) (addr (VG.Proof.Blake2.X86.Stream.Init.esp₀ s₀) d) 4 :=
  ⟨VG.Proof.Blake2.X86.Stream.Init.argR s₀, by simp [hrd, hp.rd], hp.arg_in h₁ h₂⟩

/-- The arguments are kept by writes to the state. -/
theorem arg_keep {m : Mem} (hf : Frame [VG.Proof.Blake2.X86.Stream.Init.stR s₀ w] s₀.mem m) {d : Nat} (h₁ : 4 ≤ d) (h₂ : d + 4 ≤ 20) :
    m.readW (addr (VG.Proof.Blake2.X86.Stream.Init.esp₀ s₀) d) 32 = s₀.mem.readW (addr (VG.Proof.Blake2.X86.Stream.Init.esp₀ s₀) d) 32 :=
  hf.readW (r := ⟨addr (VG.Proof.Blake2.X86.Stream.Init.esp₀ s₀) d, 4⟩) (Region.contains_self _ _)
    (by simpa using hp.a_st.sub_left (hp.arg_sub h₁ h₂)) (by decide)

theorem st_in {s : State} (hwr : s.wr = s₀.wr) {d n : Nat} (hd : d + n ≤ bufOff w + blockBytes w) (hn : 0 < n) :
    InRegions s.wr (addr (VG.Proof.Blake2.X86.Stream.Init.st s₀) d) n :=
  ⟨VG.Proof.Blake2.X86.Stream.Init.stR s₀ w, by simp [hwr, hp.wr], contains_addr hd hn hp.st_fit⟩

theorem st_inr {s : State} (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) {d n : Nat}
    (hd : d + n ≤ bufOff w + blockBytes w) (hn : 0 < n) : InRegions (s.rd ++ s.wr) (addr (VG.Proof.Blake2.X86.Stream.Init.st s₀) d) n :=
  ⟨VG.Proof.Blake2.X86.Stream.Init.stR s₀ w, by simp [hrd, hwr, hp.wr], contains_addr hd hn hp.st_fit⟩

end Pre

/-! ## Bytes -/

theorem writeW_eq (m : Mem) (a : Addr) (v : BitVec 32) : m.writeW a v = VG.WriteBytes.writeBytes m a (wordBytes v) := by
  rw [Mem.writeW, VG.WriteBytes.write_eq_writeBytes]; rfl

theorem wordBytes_zero : wordBytes (0 : BitVec 32) = List.replicate 4 0 := by decide

theorem writeBytes_at (m : Mem) (q : Addr) (xs : List Byte) {i : Nat} (hi : i < 2 ^ 64) :
    VG.WriteBytes.writeBytes m q xs (q + BitVec.ofNat 64 i) = if i < xs.length then xs.getD i 0 else m (q + BitVec.ofNat 64 i) := by
  simp only [VG.WriteBytes.writeBytes]
  rw [show q + BitVec.ofNat 64 i - q = BitVec.ofNat 64 i by rw [BitVec.add_comm]; exact BitVec.add_sub_cancel _ _,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi]

/-- The bytes at `q` after writing `xs` there: `xs`, then what was there. -/
theorem bytesAt_writeBytes_prefix (m : Mem) (q : Addr) {xs : List Byte} {n : Nat} (h : xs.length ≤ n)
    (hn : n < 2 ^ 64) :
    bytesAt (VG.WriteBytes.writeBytes m q xs) q n = xs ++ bytesAt m (q + BitVec.ofNat 64 xs.length) (n - xs.length) := by
  apply List.ext_getElem (by rw [List.length_append]; simp only [bytesAt, List.length_map, List.length_range]; omega)
  intro i h1 _
  simp only [bytesAt, List.length_map, List.length_range] at h1
  simp only [bytesAt, List.getElem_map, List.getElem_range, VG.Proof.Blake2.X86.Stream.Init.writeBytes_at m q xs (by omega : i < 2 ^ 64)]
  by_cases hi : i < xs.length
  · simp [hi, List.getElem_append_left, List.getD_eq_getElem?_getD]
  · rw [List.getElem_append_right (by omega)]
    simp only [hi, ↓reduceIte, List.getElem_map, List.getElem_range, Offset.add_ofNat_add_ofNat,
      show xs.length + (i - xs.length) = i by omega]

/-- The bytes of a run of zeros written at `q`. -/
theorem bytesAt_writeBytes_zeros (m : Mem) (q : Addr) {n a : Nat} (ha : a ≤ n) (hn : n < 2 ^ 64) :
    bytesAt (VG.WriteBytes.writeBytes m q (List.replicate n 0)) (q + BitVec.ofNat 64 a) (n - a) = List.replicate (n - a) 0 := by
  apply List.ext_getElem (by simp [bytesAt])
  intro i h1 _
  simp only [bytesAt, List.length_map, List.length_range] at h1
  simp only [bytesAt, List.getElem_map, List.getElem_range, Offset.add_ofNat_add_ofNat,
    VG.Proof.Blake2.X86.Stream.Init.writeBytes_at m q _ (by omega : a + i < 2 ^ 64), List.length_replicate, show a + i < n by omega,
    ↓reduceIte, List.getD_eq_getElem?_getD, List.getElem?_replicate, List.getElem_replicate]
  simp

/-! ## The key block -/

/-- During the zero stores. -/
def ZS (s₁ : State) (q : Addr) (j : Nat) (s : State) : Prop :=
  s.gpr = s₁.gpr ∧ s.rd = s₁.rd ∧ s.wr = s₁.wr ∧ s.mem = VG.WriteBytes.writeBytes s₁.mem q (List.replicate (4 * j) 0)

theorem zeros_ok {s₀ : State} (hp : VG.Proof.Blake2.X86.Stream.Init.Pre P s₀) {s₁ : State} (hax : s₁.gpr .eax = VG.Proof.Blake2.X86.Stream.Init.st s₀) (hdx : s₁.gpr .edx = 0)
    (hwr : s₁.wr = s₀.wr) :
    WP isa (.block ((List.range (B w / 4)).flatMap fun j => [.store (at_ .eax (VG.Impl.Blake2.X86.Stream.N w + 4 * j)) .edx])) s₁
      (VG.Proof.Blake2.X86.Stream.Init.ZS s₁ (VG.Proof.Blake2.X86.Stream.Init.stA s₀ + BitVec.ofNat 64 (bufOff w)) (B w / 4)) := by
  have fS := hp.st_fit
  refine wp_range_flatMap (M := isa) (VG.Proof.Blake2.X86.Stream.Init.ZS s₁ (VG.Proof.Blake2.X86.Stream.Init.stA s₀ + BitVec.ofNat 64 (bufOff w)))
    (fun j s hj ⟨hg, hrd, hwr', hm⟩ => ?_) _ (Nat.le_refl _) s₁
    ⟨rfl, rfl, rfl, by rw [Nat.mul_zero, List.replicate_zero, VG.WriteBytes.writeBytes_nil]⟩
  rw [VG.Proof.Blake2.X86.Stream.B_eq] at hj
  rw [VG.Proof.Blake2.X86.Stream.N_eq]
  have hj4 : bufOff w + 4 * j + 4 ≤ bufOff w + blockBytes w := by omega
  refine wp_stm (B := VG.Proof.Blake2.X86.Stream.Init.st s₀) (by rw [hg, hax]) (by rw [hwr', hwr]; exact hp.st_in rfl hj4 (by omega))
    fun s' u' => WP.block_nil ⟨by rw [u'.gpr, hg], by rw [u'.rd, hrd], by rw [u'.wr, hwr'], ?_⟩
  rw [u'.mem, hm, hg, hdx, addr_eq (by omega), VG.Proof.Blake2.X86.Stream.Init.writeW_eq, VG.Proof.Blake2.X86.Stream.Init.wordBytes_zero, ← Offset.add_add]
  have e := VG.WriteBytes.writeBytes_append s₁.mem (VG.Proof.Blake2.X86.Stream.Init.stA s₀ + BitVec.ofNat 64 (bufOff w)) (List.replicate (4 * j) 0)
    (List.replicate 4 0) (by simp; omega)
  rw [List.length_replicate] at e
  rw [e, List.replicate_append_replicate, Nat.mul_succ]

/-- After the key block (or none): our caller's `ebx`, `esi`, `edi`, `ebp`
and `esp` are kept, only the state is written, and the buffer holds the key,
padded with zeros, if there is one. -/
structure KB (P : VG.Spec.Blake2.Params w) (s₀ s : State) : Prop where
  gpr : ∀ r ∈ calleeSaved, s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [VG.Proof.Blake2.X86.Stream.Init.stR s₀ w] s₀.mem s.mem
  buf : VG.Proof.Blake2.X86.Stream.Init.kk s₀ ≠ 0 → bytesAt s.mem (VG.Proof.Blake2.X86.Stream.Init.stA s₀ + BitVec.ofNat 64 (bufOff w)) (blockBytes w) =
    VG.Proof.Blake2.X86.Stream.Init.K s₀ ++ List.replicate (blockBytes w - VG.Proof.Blake2.X86.Stream.Init.kk s₀) 0

theorem keyBlock_ok (hP : VG.Proof.Blake2.X86.Stream.Ok P) {s₀ : State} (hp : VG.Proof.Blake2.X86.Stream.Init.Pre P s₀) (hk : VG.Proof.Blake2.X86.Stream.Init.kk s₀ ≠ 0) {s : State}
    (hax : s.gpr .eax = VG.Proof.Blake2.X86.Stream.Init.st s₀) (hcx : s.gpr .ecx = VG.X86.arg s₀ 3)
    (hg : ∀ r ∈ calleeSaved, s.gpr r = s₀.gpr r) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (hm : s.mem = s₀.mem) :
    WP isa (Impl.Blake2.X86.Stream.keyBlock (w := w)) s (VG.Proof.Blake2.X86.Stream.Init.KB P s₀) := by
  have hl := hP.len
  have hN := hP.N
  have hmx := hP.max
  have hkk := hp.kk_hi
  have hpos := hP.pos
  have hbb := hP.bb
  have fS := hp.st_fit; have fK := hp.key_fit
  unfold Impl.Blake2.X86.Stream.keyBlock
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine wp_movi fun s₁ u₁ => ?_
  refine WP.mono (VG.Proof.Blake2.X86.Stream.Init.zeros_ok hp (by rw [u₁.other _ (by decide), hax]) u₁.gpr (by rw [u₁.wr, hwr]))
    fun s₂ ⟨g₂, rd₂, wr₂, m₂⟩ => ?_
  rw [VG.Proof.Blake2.X86.Stream.B_eq, show 4 * (blockBytes w / 4) = blockBytes w by rcases hP.bb with h | h <;> omega] at m₂
  have ax₂ : s₂.gpr .eax = VG.Proof.Blake2.X86.Stream.Init.st s₀ := by rw [g₂, u₁.other _ (by decide), hax]
  refine wp_stm (o := 0) ax₂ (by rw [wr₂, u₁.wr, hwr]; exact hp.st_in rfl (by omega) (by omega)) fun s₃ u₃ => ?_
  have sp₃ : s₃.gpr .esp = VG.Proof.Blake2.X86.Stream.Init.esp₀ s₀ := by rw [u₃.gpr, g₂, u₁.other _ (by decide), hg _ (by decide)]
  have rd₃ : s₃.rd = s₀.rd := by rw [u₃.rd, rd₂, u₁.rd, hrd]
  have wr₃ : s₃.wr = s₀.wr := by rw [u₃.wr, wr₂, u₁.wr, hwr]
  have m₃ : s₃.mem = (VG.WriteBytes.writeBytes s₀.mem (VG.Proof.Blake2.X86.Stream.Init.stA s₀ + BitVec.ofNat 64 (bufOff w))
      (List.replicate (blockBytes w) 0)).writeW (addr (VG.Proof.Blake2.X86.Stream.Init.st s₀) 0) (s₀.gpr .ebx) := by
    rw [u₃.mem, m₂, u₁.mem, hm, g₂, u₁.other _ (by decide), hg _ (by decide)]
  have F₃ : Frame [VG.Proof.Blake2.X86.Stream.Init.stR s₀ w] s₀.mem s₃.mem := by
    rw [m₃]
    exact (VG.WriteBytes.writeBytes_frame _ _ _ (contains_offset (by simp only [List.length_replicate]; omega) (by omega))).writeW
      (List.mem_singleton_self _) _ (contains_addr (by omega) (by omega) fS)
  refine wp_ldm sp₃ (hp.rin rd₃ (d := 12) (by omega) (by omega)) fun s₄ u₄ => WP.block_nil ?_
  have dx₄ : s₄.gpr .edx = VG.Proof.Blake2.X86.Stream.Init.key s₀ := by rw [u₄.gpr, hp.arg_keep F₃ (by omega) (by omega)]; rfl
  have m₄ : s₄.mem = s₃.mem := u₄.mem
  -- The copy.
  have hk32 : VG.Proof.Blake2.X86.Stream.Init.kk s₀ < 2 ^ 32 := (VG.X86.arg s₀ 3).isLt
  refine WP.seq (VG.Proof.Blake2.X86.Stream.copyLoop_ok (w := w) (tmp := .bl) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (dA := VG.Proof.Blake2.X86.Stream.Init.st s₀) (sA := VG.Proof.Blake2.X86.Stream.Init.key s₀) (k := VG.Proof.Blake2.X86.Stream.Init.kk s₀) (by omega) hk32 (by omega) (by omega) dx₄
    (by rw [u₄.other _ (by decide), u₃.gpr, ax₂])
    (by rw [u₄.other _ (by decide), u₃.gpr, g₂, u₁.other _ (by decide), hcx]; simp)
    (fun i hi => ⟨VG.Proof.Blake2.X86.Stream.Init.keyR s₀, by simp [u₄.rd, rd₃, hp.rd], contains_offset (by omega) (by omega)⟩)
    (fun i hi => by
      rw [u₄.wr, wr₃, addr_eq (by omega)]
      exact ⟨VG.Proof.Blake2.X86.Stream.Init.stR s₀ w, by simp [hp.wr], by rw [Offset.add_add]; exact contains_offset (by omega) (by omega)⟩)
    (by rw [addr_eq (by omega)]; exact hp.key_st.sub_right (sub_offset (by omega) (by omega)))
    fun s₅ h₅ => ?_)
  -- The bytes copied are the key's, and the spill is outside them.
  have hK : bytesAt s₄.mem (VG.Proof.Blake2.X86.Stream.Init.keyA s₀) (VG.Proof.Blake2.X86.Stream.Init.kk s₀) = VG.Proof.Blake2.X86.Stream.Init.K s₀ :=
    bytesAt_congr fun i hi => by
      rw [m₄]
      exact F₃.bytes (R := VG.Proof.Blake2.X86.Stream.Init.keyR s₀) (by simpa using hp.key_st) (by simp only; omega) hi
  have hm₅ := h₅.mem
  rw [List.take_of_length_le (by simp [bytesAt]), hK, m₄, addr_eq (by omega)] at hm₅
  have rd₅ : s₅.rd = s₀.rd := by rw [h₅.rd, u₄.rd, rd₃]
  have wr₅ : s₅.wr = s₀.wr := by rw [h₅.wr, u₄.wr, wr₃]
  refine wp_ldm (b := .esp) (by rw [h₅.other _ (by decide) (by decide) (by decide) (by decide), u₄.other _ (by decide), sp₃])
    (hp.rin rd₅ (d := 4) (by omega) (by omega)) fun s₆ u₆ => ?_
  have F₅ : Frame [VG.Proof.Blake2.X86.Stream.Init.stR s₀ w] s₀.mem s₅.mem := by
    rw [hm₅]
    exact F₃.trans (VG.WriteBytes.writeBytes_frame _ _ _ (by
      simp only [bytesAt, List.length_map, List.length_range]; exact contains_offset (by omega) (by omega)))
  have ax₆ : s₆.gpr .eax = VG.Proof.Blake2.X86.Stream.Init.st s₀ := by rw [u₆.gpr, hp.arg_keep F₅ (by omega) (by omega)]; rfl
  refine wp_ldm ax₆ (by rw [u₆.rd, u₆.wr, rd₅, wr₅]; exact hp.st_inr rfl rfl (by omega) (by omega))
    fun s₇ u₇ => WP.block_nil ?_
  have m₇ : s₇.mem = s₅.mem := by rw [u₇.mem, u₆.mem]
  -- The spilled `ebx`, outside the buffer.
  have hbx : s₅.mem.readW (addr (VG.Proof.Blake2.X86.Stream.Init.st s₀) 0) 32 = s₀.gpr .ebx := by
    rw [hm₅, m₃]
    rw [(VG.WriteBytes.writeBytes_frame (R := ⟨VG.Proof.Blake2.X86.Stream.Init.stA s₀ + BitVec.ofNat 64 (bufOff w), blockBytes w⟩) _ _ _ (by
      simp only [bytesAt, List.length_map, List.length_range]
      exact Offset.contains _ (Nat.le_refl _) (by omega) (by omega))).readW
      (r := ⟨addr (VG.Proof.Blake2.X86.Stream.Init.st s₀) 0, 4⟩) (Region.contains_self _ _) ?_ (by decide), Mem.readW_writeW_self32]
    simp only [List.mem_singleton, forall_eq]
    rw [addr_eq (by omega)]
    exact Offset.disjoint (VG.Proof.Blake2.X86.Stream.Init.stA s₀) (by omega) (by omega) (by omega)
  refine ⟨fun r hr => ?_, by rw [u₇.rd, u₆.rd, rd₅], by rw [u₇.wr, u₆.wr, wr₅],
    by rw [m₇]; exact F₅, fun _ => ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [u₇.gpr, u₆.mem, hbx]
    all_goals
      rw [u₇.other _ (by decide), u₆.other _ (by decide), h₅.other _ (by decide) (by decide) (by decide) (by decide),
        u₄.other _ (by decide), u₃.gpr, g₂, u₁.other _ (by decide), hg _ (by decide)]
  · have hKl : (VG.Proof.Blake2.X86.Stream.Init.K s₀).length = VG.Proof.Blake2.X86.Stream.Init.kk s₀ := by simp [bytesAt]
    rw [m₇, hm₅, m₃, VG.Proof.Blake2.X86.Stream.Init.bytesAt_writeBytes_prefix _ _ (by rw [hKl]; omega) (by omega), hKl]
    refine congrArg (VG.Proof.Blake2.X86.Stream.Init.K s₀ ++ ·) ?_
    rw [← VG.Proof.Blake2.X86.Stream.Init.bytesAt_writeBytes_zeros s₀.mem (VG.Proof.Blake2.X86.Stream.Init.stA s₀ + BitVec.ofNat 64 (bufOff w)) (a := VG.Proof.Blake2.X86.Stream.Init.kk s₀)
      (n := blockBytes w) (by omega) (by omega)]
    have hf : Frame [⟨addr (VG.Proof.Blake2.X86.Stream.Init.st s₀) 0, 4⟩] (VG.WriteBytes.writeBytes s₀.mem (VG.Proof.Blake2.X86.Stream.Init.stA s₀ + BitVec.ofNat 64 (bufOff w))
        (List.replicate (blockBytes w) 0)) ((VG.WriteBytes.writeBytes s₀.mem (VG.Proof.Blake2.X86.Stream.Init.stA s₀ + BitVec.ofNat 64 (bufOff w))
        (List.replicate (blockBytes w) 0)).writeW (addr (VG.Proof.Blake2.X86.Stream.Init.st s₀) 0) (s₀.gpr .ebx)) :=
      (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
    refine bytesAt_congr fun i hi => ?_
    refine hf.bytes (R := ⟨VG.Proof.Blake2.X86.Stream.Init.stA s₀ + BitVec.ofNat 64 (bufOff w) + BitVec.ofNat 64 (VG.Proof.Blake2.X86.Stream.Init.kk s₀), blockBytes w - VG.Proof.Blake2.X86.Stream.Init.kk s₀⟩)
      ?_ (by simp only; omega) hi
    simp only [List.mem_singleton, forall_eq]
    rw [addr_eq (by omega), Offset.add_add]
    exact Offset.disjoint (VG.Proof.Blake2.X86.Stream.Init.stA s₀) (by omega) (by omega) (by omega)

/-! ## The initial hash value -/

theorem wp_xori {is : List Instr} {s : State} {Q : State → Prop} {d : Reg} {v : BitVec 32}
    (k : ∀ s', Upd s s' d (s.gpr d ^^^ v) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .xor d (.imm v) :: is)) s Q :=
  cons rfl (k _ (Upd.flags _ _ _ _ _ _))

/-- During the stores of the IV. -/
def WS (P : VG.Spec.Blake2.Params w) (st : BitVec 32) (s₁ : State) (j : Nat) (s : State) : Prop :=
  (∀ r, r ≠ .ecx → s.gpr r = s₁.gpr r) ∧ s.rd = s₁.rd ∧ s.wr = s₁.wr ∧
    Frame [⟨st.setWidth 64, bufOff w⟩] s₁.mem s.mem ∧ ∀ i < j, s.mem.readW (addr st (4 * i)) 32 = ivWord P i

theorem words_ok (hP : VG.Proof.Blake2.X86.Stream.Ok P) {s₀ : State} (hp : VG.Proof.Blake2.X86.Stream.Init.Pre P s₀) {s₁ : State} (hax : s₁.gpr .eax = VG.Proof.Blake2.X86.Stream.Init.st s₀)
    (hwr : s₁.wr = s₀.wr) :
    WP isa (.block ((List.range (VG.Impl.Blake2.X86.Stream.N w / 4)).flatMap fun k =>
      [.mov .ecx (.imm (ivWord P k)), .store (at_ .eax (4 * k)) .ecx])) s₁ (VG.Proof.Blake2.X86.Stream.Init.WS P (VG.Proof.Blake2.X86.Stream.Init.st s₀) s₁ (VG.Impl.Blake2.X86.Stream.N w / 4)) := by
  have fS := hp.st_fit
  have hl := hP.len
  have hbb := hP.bb
  refine wp_range_flatMap (M := isa) (VG.Proof.Blake2.X86.Stream.Init.WS P (VG.Proof.Blake2.X86.Stream.Init.st s₀) s₁) (fun k s hk ⟨hg, hrd, hwr', hf, hv⟩ => ?_) _
    (Nat.le_refl _) s₁ ⟨fun _ _ => rfl, rfl, rfl, Frame.refl _ _, fun _ h => absurd h (by omega)⟩
  rw [VG.Proof.Blake2.X86.Stream.N_eq] at hk
  have hN : bufOff w = blockBytes w / 2 := hP.N
  have hk4 : 4 * k + 4 ≤ bufOff w := by omega
  refine wp_movi fun s₂ u₂ => wp_stm (B := VG.Proof.Blake2.X86.Stream.Init.st s₀) (by rw [u₂.other _ (by decide), hg _ (by decide), hax])
    (by rw [u₂.wr, hwr', hwr]; exact hp.st_in rfl (by omega) (by omega)) fun s₃ u₃ => WP.block_nil ?_
  refine ⟨fun r hr => by rw [u₃.gpr, u₂.other r hr, hg r hr], by rw [u₃.rd, u₂.rd, hrd],
    by rw [u₃.wr, u₂.wr, hwr'], ?_, fun i hi => ?_⟩
  · rw [u₃.mem, u₂.mem]
    exact hf.writeW (List.mem_singleton_self _) _ (contains_addr (by omega) (by omega) (by omega))
  · rw [u₃.mem, u₂.gpr, u₂.mem]
    by_cases e : i = k
    · subst e; rw [Mem.readW_writeW_self32]
    · rw [MdStream.X86.readW_writeW_addr _ _ (by omega) (by omega) (by omega)]
      exact hv i (by omega)

theorem rot24 {kk : Nat} (h : kk < 2 ^ 24) :
    (BitVec.ofNat 32 kk).rotateRight 24 = BitVec.ofNat 32 kk <<< 8 := by
  rw [BitVec.rotateRight_def]
  have e : BitVec.ofNat 32 kk >>> (24 % 32) = 0#32 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (by omega)]
    show kk / 2 ^ (24 % 32) = 0
    exact Nat.div_eq_of_lt (by simpa using h)
  rw [e, BitVec.zero_or]

theorem getElem!_IV (P : VG.Spec.Blake2.Params w) {i : Nat} (hi : i < 8) : P.IV[i]! = P.IV[i] := by
  simp [hi]

theorem ivWord32 (P : VG.Spec.Blake2.Params 32) {i : Nat} (hi : i < 8) : ivWord P i = P.IV[i] := by
  simp only [ivWord, Nat.reduceDiv, Nat.div_one, Nat.mod_one, Nat.mul_zero, VG.Proof.Blake2.X86.Stream.Init.getElem!_IV P hi,
    BitVec.extractLsb'_eq_self]

theorem ivWord64_lo (P : VG.Spec.Blake2.Params 64) {i : Nat} (hi : i < 8) :
    ivWord P (2 * i) = Proof.Sha512.Word64.lo P.IV[i] := by
  simp only [ivWord, Nat.reduceDiv, Nat.mul_div_cancel_left _ (by decide : 0 < 2), Nat.mul_mod_right,
    Nat.mul_zero, VG.Proof.Blake2.X86.Stream.Init.getElem!_IV P hi, Proof.Sha512.Word64.lo]

theorem ivWord64_hi (P : VG.Spec.Blake2.Params 64) {i : Nat} (hi : i < 8) :
    ivWord P (2 * i + 1) = Proof.Sha512.Word64.hi P.IV[i] := by
  have e : (2 * i + 1) / 2 = i := by omega
  have e' : (2 * i + 1) % 2 = 1 := by omega
  simp only [ivWord, Nat.reduceDiv, e, e', Nat.mul_one, VG.Proof.Blake2.X86.Stream.Init.getElem!_IV P hi, Proof.Sha512.Word64.hi]

theorem lohi (X : BitVec 64) (x : BitVec 32) (h : X.toNat = x.toNat) :
    Proof.Sha512.Word64.lo X = x ∧ Proof.Sha512.Word64.hi X = 0 := by
  have := x.isLt
  refine ⟨BitVec.eq_of_toNat_eq ?_, BitVec.eq_of_toNat_eq ?_⟩
  · rw [Proof.Sha512.Word64.lo_toNat, h, Nat.mod_eq_of_lt this]
  · rw [Proof.Sha512.Word64.hi_toNat, h, Nat.div_eq_of_lt this]; rfl

/-- The initial hash value, from the words stored. -/
theorem stateAt_init (hP : VG.Proof.Blake2.X86.Stream.Ok P) {m : Mem} {st : BitVec 32} (hfit : st.toNat + bufOff w ≤ 2 ^ 32)
    {kk nn : Nat} (hkk : kk < 2 ^ 24) (hnn : nn < 2 ^ 32)
    (h0 : m.readW (addr st 0) 32 =
      ((ivWord P 0 ^^^ 0x01010000) ^^^ (BitVec.ofNat 32 kk).rotateRight 24) ^^^ BitVec.ofNat 32 nn)
    (h : ∀ i, 1 ≤ i → i < bufOff w / 4 → m.readW (addr st (4 * i)) 32 = ivWord P i) :
    stateAt w m (st.setWidth 64) = init P nn kk := by
  apply Vector.ext
  intro j hj
  simp only [stateAt, Vector.getElem_ofFn, Spec.Blake2.init, Vector.getElem_set]
  rcases hP.w with rfl | rfl
  · -- 64-bit words: two 32-bit words each.
    have e₀ : addr st (8 * j) = st.setWidth 64 + BitVec.ofNat 64 (64 / 8 * j) := addr_eq (by simp [bufOff] at hfit; omega)
    have e₁ : addr st (8 * j + 4) = st.setWidth 64 + BitVec.ofNat 64 (64 / 8 * j) + 4 := by
      rw [addr_eq (by simp [bufOff] at hfit; omega), show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl,
        Offset.add_ofNat_add_ofNat]
    rw [Proof.Sha512.Word64.readW64, ← e₁, ← e₀, show 8 * j = 4 * (2 * j) by omega,
      show 4 * (2 * j) + 4 = 4 * (2 * j + 1) by omega]
    have hhi := h (2 * j + 1) (by omega) (by simp [bufOff]; omega)
    rw [hhi, VG.Proof.Blake2.X86.Stream.Init.ivWord64_hi P hj]
    by_cases e : j = 0
    · subst e
      simp only [Nat.mul_zero, ↓reduceIte] at h0 ⊢
      have l0 := VG.Proof.Blake2.X86.Stream.Init.ivWord64_lo P (i := 0) (by decide)
      rw [Nat.mul_zero] at l0
      rw [h0, l0, VG.Proof.Blake2.X86.Stream.Init.rot24 hkk]
      have hC := VG.Proof.Blake2.X86.Stream.Init.lohi (((16842752 : Nat) : BitVec 64)) (0x01010000 : BitVec 32) rfl
      have hK := VG.Proof.Blake2.X86.Stream.Init.lohi (BitVec.ofNat 64 kk <<< 8) (BitVec.ofNat 32 kk <<< 8) (by
        simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]; omega)
      have hN := VG.Proof.Blake2.X86.Stream.Init.lohi (BitVec.ofNat 64 nn) (BitVec.ofNat 32 nn) (by simp only [BitVec.toNat_ofNat]; omega)
      refine Proof.Sha512.Word64.eq_of_lo_hi ?_ ?_
      · rw [Proof.Sha512.Word64.lo_append, Proof.Sha512.Word64.lo_xor, Proof.Sha512.Word64.lo_xor,
          Proof.Sha512.Word64.lo_xor, hC.1, hK.1, hN.1]
      · rw [Proof.Sha512.Word64.hi_append, Proof.Sha512.Word64.hi_xor, Proof.Sha512.Word64.hi_xor,
          Proof.Sha512.Word64.hi_xor, hC.2, hK.2, hN.2]; simp
    · rw [h (2 * j) (by omega) (by simp [bufOff]; omega), VG.Proof.Blake2.X86.Stream.Init.ivWord64_lo P hj,
        Proof.Sha512.Word64.hi_append_lo]
      simp [Ne.symm e]
  · have e₀ : addr st (4 * j) = st.setWidth 64 + BitVec.ofNat 64 (32 / 8 * j) := addr_eq (by simp [bufOff] at hfit; omega)
    rw [← e₀]
    by_cases e : j = 0
    · subst e
      simp only [Nat.mul_zero, ↓reduceIte]
      rw [h0, VG.Proof.Blake2.X86.Stream.Init.ivWord32 P (by decide), VG.Proof.Blake2.X86.Stream.Init.rot24 hkk]; rfl
    · rw [h j (by omega) (by simp [bufOff]; omega), VG.Proof.Blake2.X86.Stream.Init.ivWord32 P hj]
      simp [Ne.symm e]

theorem initState_ok (hP : VG.Proof.Blake2.X86.Stream.Ok P) {s₀ : State} (hp : VG.Proof.Blake2.X86.Stream.Init.Pre P s₀) {s : State} (hrd : s.rd = s₀.rd)
    (hwr : s.wr = s₀.wr) (hsp : s.gpr .esp = VG.Proof.Blake2.X86.Stream.Init.esp₀ s₀) (hf : Frame [VG.Proof.Blake2.X86.Stream.Init.stR s₀ w] s₀.mem s.mem) :
    WP isa (.block (.mov .eax (.mem (at_ .esp 4)) :: initState P)) s fun s' =>
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [⟨VG.Proof.Blake2.X86.Stream.Init.stA s₀, bufOff w⟩] s.mem s'.mem ∧ stateAt w s'.mem (VG.Proof.Blake2.X86.Stream.Init.stA s₀) = Spec.Blake2.init P (VG.Proof.Blake2.X86.Stream.Init.nn s₀) (VG.Proof.Blake2.X86.Stream.Init.kk s₀) := by
  have hl := hP.len
  have hbb := hP.bb
  have hN := hP.N
  have fS := hp.st_fit
  have hkk := hp.kk_hi
  have hmx := hP.max
  refine wp_ldm hsp (hp.rin hrd (d := 4) (by omega) (by omega)) fun s₁ u₁ => ?_
  have ax₁ : s₁.gpr .eax = VG.Proof.Blake2.X86.Stream.Init.st s₀ := by rw [u₁.gpr, hp.arg_keep hf (by omega) (by omega)]; rfl
  unfold initState
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Blake2.X86.Stream.Init.words_ok hP hp ax₁ (by rw [u₁.wr, hwr])) fun s₂ ⟨g₂, rd₂, wr₂, f₂, v₂⟩ => ?_
  have ax₂ : s₂.gpr .eax = VG.Proof.Blake2.X86.Stream.Init.st s₀ := by rw [g₂ _ (by decide), ax₁]
  have hN4 : 0 < VG.Impl.Blake2.X86.Stream.N w / 4 := by rw [VG.Proof.Blake2.X86.Stream.N_eq]; omega
  have f₂' : Frame [VG.Proof.Blake2.X86.Stream.Init.stR s₀ w] s₁.mem s₂.mem := f₂.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨VG.Proof.Blake2.X86.Stream.Init.stR s₀ w, by simp, Region.sub_prefix (by omega)⟩
  have F₂ : Frame [VG.Proof.Blake2.X86.Stream.Init.stR s₀ w] s₀.mem s₂.mem := hf.trans (u₁.mem ▸ f₂')
  have rd₂' : s₂.rd = s₀.rd := by rw [rd₂, u₁.rd, hrd]
  have wr₂' : s₂.wr = s₀.wr := by rw [wr₂, u₁.wr, hwr]
  have sp₂ : s₂.gpr .esp = VG.Proof.Blake2.X86.Stream.Init.esp₀ s₀ := by rw [g₂ _ (by decide), u₁.other _ (by decide), hsp]
  refine wp_ldm ax₂ (hp.st_inr rd₂' wr₂' (by omega) (by omega)) fun s₃ u₃ => ?_
  refine VG.Proof.Blake2.X86.Stream.Init.wp_xori fun s₄ u₄ => ?_
  refine wp_ldm (by rw [u₄.other _ (by decide), u₃.other _ (by decide), sp₂])
    (by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr]; exact hp.rin rd₂' (d := 16) (by omega) (by omega)) fun s₅ u₅ => ?_
  refine wp_ror ⟨by decide, by decide⟩ fun s₆ u₆ => wp_xor fun s₇ u₇ => ?_
  have i8 := hp.rin rd₂' (d := 8) (by omega) (by omega)
  refine wp_xorm (b := .esp) (by rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
    u₄.other _ (by decide), u₃.other _ (by decide), sp₂])
    (by rw [u₇.rd, u₇.wr, u₆.rd, u₆.wr, u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd, u₃.wr]; exact i8) fun s₈ u₈ => ?_
  refine wp_stm (o := 0) (by rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
    u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), ax₂])
    (by rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr]; exact hp.st_in wr₂' (by omega) (by omega))
    fun s₉ u₉ => WP.block_nil ?_
  have hm₈ : s₈.mem = s₂.mem := by rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem]
  have a16 : s₅.gpr .edx = VG.X86.arg s₀ 3 := by
    rw [u₅.gpr, u₄.mem, u₃.mem, hp.arg_keep F₂ (by omega) (by omega)]; rfl
  have a8 : s₇.mem.readW (addr (VG.Proof.Blake2.X86.Stream.Init.esp₀ s₀) 8) 32 = VG.X86.arg s₀ 1 := by
    rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, hp.arg_keep F₂ (by omega) (by omega)]; rfl
  have v₀ : s₂.mem.readW (addr (VG.Proof.Blake2.X86.Stream.Init.st s₀) 0) 32 = ivWord P 0 := v₂ 0 hN4
  have hV : s₈.gpr .ecx = ((ivWord P 0 ^^^ 0x01010000) ^^^ (BitVec.ofNat 32 (VG.Proof.Blake2.X86.Stream.Init.kk s₀)).rotateRight 24) ^^^
      BitVec.ofNat 32 (VG.Proof.Blake2.X86.Stream.Init.nn s₀) := by
    rw [u₈.gpr, a8, u₇.gpr, u₆.gpr, u₆.other _ (by decide), u₅.other _ (by decide), a16, u₄.gpr, u₃.gpr, v₀]
    simp
  have hm₉ : s₉.mem = s₂.mem.writeW (addr (VG.Proof.Blake2.X86.Stream.Init.st s₀) 0) (s₈.gpr .ecx) := by rw [u₉.mem, hm₈]
  refine ⟨fun r h1 h2 h3 => ?_, by rw [u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, rd₂, u₁.rd],
    by rw [u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, wr₂, u₁.wr], ?_, ?_⟩
  · rw [u₉.gpr, u₈.other r h2, u₇.other r h2, u₆.other r h3, u₅.other r h3, u₄.other r h2, u₃.other r h2,
      g₂ r h2, u₁.other r h1]
  · rw [hm₉, ← u₁.mem]
    exact f₂.writeW (List.mem_singleton_self _) _ (contains_addr (by omega) (by omega) (by omega))
  · rw [hm₉]
    refine VG.Proof.Blake2.X86.Stream.Init.stateAt_init hP (by omega) (by omega) (by have := (VG.X86.arg s₀ 1).isLt; omega)
      (by rw [Mem.readW_writeW_self32, hV]) fun i h1 h2 => ?_
    rw [MdStream.X86.readW_writeW_addr _ _ (by omega) (by omega) (by omega)]
    exact v₂ i (by rw [VG.Proof.Blake2.X86.Stream.N_eq]; omega)

/-! ## The whole function -/

theorem correct (hP : VG.Proof.Blake2.X86.Stream.Ok P) {s₀ : State} (hp : VG.Proof.Blake2.X86.Stream.Init.Pre P s₀) :
    WP isa (Impl.Blake2.X86.Stream.init P) s₀ fun s' => abiPreserved s₀ s' ∧ (initX86 P).post s₀ s' := by
  have hl := hP.len
  have hkk := hp.kk_hi
  have hmx := hP.max
  unfold Impl.Blake2.X86.Stream.init
  refine WP.seq (wp_ldm rfl (hp.rin rfl (d := 4) (by omega) (by omega)) fun s₁ u₁ => ?_)
  refine wp_ldm (by rw [u₁.other _ (by decide)]) (by rw [u₁.rd, u₁.wr]; exact hp.rin rfl (d := 16) (by omega) (by omega))
    fun s₂ u₂ => wp_test fun s₃ f₃ z₃ => WP.block_nil ?_
  have ax₃ : s₃.gpr .eax = VG.Proof.Blake2.X86.Stream.Init.st s₀ := by rw [f₃.gpr, u₂.other _ (by decide), u₁.gpr]; rfl
  have cx₃ : s₃.gpr .ecx = VG.X86.arg s₀ 3 := by rw [f₃.gpr, u₂.gpr, u₁.mem]; rfl
  have g₃ : ∀ r ∈ calleeSaved, s₃.gpr r = s₀.gpr r := fun r hr => by
    rw [f₃.gpr, u₂.other r (by simp [calleeSaved] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide),
      u₁.other r (by simp [calleeSaved] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)]
  have rd₃ : s₃.rd = s₀.rd := by rw [f₃.rd, u₂.rd, u₁.rd]
  have wr₃ : s₃.wr = s₀.wr := by rw [f₃.wr, u₂.wr, u₁.wr]
  have m₃ : s₃.mem = s₀.mem := by rw [f₃.mem, u₂.mem, u₁.mem]
  have hz : isa.eval .e s₃ = some (decide (VG.Proof.Blake2.X86.Stream.Init.kk s₀ = 0)) := by
    show s₃.zf = _
    rw [z₃, u₂.gpr, u₁.mem, BitVec.and_self]
    show some (VG.X86.arg s₀ 3 == 0) = _
    have := ofNat_beq_zero (VG.X86.arg s₀ 3).isLt
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq] at this
    rw [this]
  refine WP.seq (WP.mono (Q := VG.Proof.Blake2.X86.Stream.Init.KB P s₀) ?_ fun s₄ hK => ?_)
  · refine WP.ite _ hz (fun hb => ?_) (fun hb => ?_)
    · simp only [decide_eq_true_eq] at hb
      exact WP.block_nil ⟨g₃, rd₃, wr₃, by rw [m₃]; exact Frame.refl _ _, fun h => absurd hb h⟩
    · simp only [decide_eq_false_iff_not] at hb
      exact VG.Proof.Blake2.X86.Stream.Init.keyBlock_ok hP hp hb ax₃ cx₃ g₃ rd₃ wr₃ m₃
  refine WP.mono (VG.Proof.Blake2.X86.Stream.Init.initState_ok hP hp hK.rd hK.wr (hK.gpr _ (by decide)) hK.frame)
    fun s₅ ⟨g₅, rd₅, wr₅, f₅, st₅⟩ => ?_
  have F : Frame [VG.Proof.Blake2.X86.Stream.Init.stR s₀ w] s₀.mem s₅.mem := hK.frame.trans (f₅.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨VG.Proof.Blake2.X86.Stream.Init.stR s₀ w, by simp, Region.sub_prefix (by omega)⟩)
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · rw [g₅ r (by simp [calleeSaved] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)
      (by simp [calleeSaved] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)
      (by simp [calleeSaved] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)]
    exact hK.gpr r hr
  · exact F.readW (Region.contains_self _ _) (by simpa using hp.ret_st) (by decide)
  · show Spec.Blake2.Repr P (Spec.Blake2.init P (VG.Proof.Blake2.X86.Stream.Init.nn s₀) (VG.Proof.Blake2.X86.Stream.Init.kk s₀)) s₅.mem (VG.Proof.Blake2.X86.Stream.Init.stA s₀) (Spec.Blake2.keyBlock w (VG.Proof.Blake2.X86.Stream.Init.K s₀))
    have hKl : (VG.Proof.Blake2.X86.Stream.Init.K s₀).length = VG.Proof.Blake2.X86.Stream.Init.kk s₀ := by simp [bytesAt]
    refine repr_keyBlock P hP.pos (by omega) st₅ fun hk => ?_
    rw [hKl] at hk ⊢
    rw [← hK.buf hk]
    refine bytesAt_congr fun i hi => ?_
    refine f₅.bytes (R := ⟨VG.Proof.Blake2.X86.Stream.Init.stA s₀ + BitVec.ofNat 64 (bufOff w), blockBytes w⟩) ?_ (by simp only; omega) hi
    simp only [List.mem_singleton, forall_eq]
    exact Offset.disjoint_base _ (Nat.le_refl _) (by have := hp.st_fit; omega)

end VG.Proof.Blake2.X86.Stream.Init

end

/- Proofs formerly in `VerifiedGarbage.Proof.Blake2.X86.Stream.Update`. -/
section

/-!
# Streaming BLAKE2 on x86 (32-bit): `update`

The functional correctness of `update`, for either word size and any correct
compression function (`CalleeOk`).
-/

namespace VG.Proof.Blake2.X86.Stream.Update

open VG VG.X86 VG.X86.Wp VG.Spec.Blake2
open VG.Impl.Blake2.X86 (at_)
open VG.Impl.Blake2.X86.Stream
open VG.Proof.Blake2 (compressX86 updateX86 countX86 ReprR bufLen_le repr_iff reprR_append reprR_flush
  reprR_blocks repr_of_reprR stateAt_congr bytesAt_congr bytesAt_add compressBlocks_congr compressBlocks_succ
  compressBlocks_zero)
open VG.WriteBytes (writeBytes writeBytes_before writeBytes_frame)
open VG.Proof.MdStream.X86 (contains_addr addr_add_ofNat sub_offset contains_offset)

variable {w : Nat} {P : VG.Spec.Blake2.Params w}

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev esp₀ : BitVec 32 := s₀.gpr .esp
abbrev st : BitVec 32 := VG.X86.arg s₀ 0
abbrev cnt : Nat := (countX86 s₀).toNat
abbrev dp : BitVec 32 := VG.X86.arg s₀ 3
abbrev len : Nat := (VG.X86.arg s₀ 4).toNat
abbrev scr : BitVec 32 := VG.X86.arg s₀ 5
abbrev stA : Addr := (VG.Proof.Blake2.X86.Stream.Update.st s₀).setWidth 64
abbrev dA : Addr := (VG.Proof.Blake2.X86.Stream.Update.dp s₀).setWidth 64
abbrev scA : Addr := (VG.Proof.Blake2.X86.Stream.Update.scr s₀).setWidth 64
abbrev stR (w : Nat) : Region := ⟨VG.Proof.Blake2.X86.Stream.Update.stA s₀, bufOff w + blockBytes w⟩
abbrev dR : Region := ⟨VG.Proof.Blake2.X86.Stream.Update.dA s₀, VG.Proof.Blake2.X86.Stream.Update.len s₀⟩
abbrev scR : Region := ⟨VG.Proof.Blake2.X86.Stream.Update.scA s₀, 576⟩
abbrev argR : Region := ⟨argAddr s₀ 0, 24⟩
abbrev retR : Region := ⟨(VG.Proof.Blake2.X86.Stream.Update.esp₀ s₀).setWidth 64, 4⟩
/-- Where the calls of the compression function push its arguments and store
the return address. -/
abbrev stkR : Region := below (VG.Proof.Blake2.X86.Stream.Update.esp₀ s₀) 32
/-- The first `c` bytes of data. -/
abbrev D (c : Nat) : List Byte := VG.Spec.Blake2.bytesAt s₀.mem (VG.Proof.Blake2.X86.Stream.Update.dA s₀) c

end

structure Pre (w : Nat) (s₀ : State) : Prop where
  rd : s₀.rd = [VG.Proof.Blake2.X86.Stream.Update.dR s₀, VG.Proof.Blake2.X86.Stream.Update.argR s₀]
  wr : s₀.wr = [VG.Proof.Blake2.X86.Stream.Update.stR s₀ w, VG.Proof.Blake2.X86.Stream.Update.scR s₀]
  st_scr : (VG.Proof.Blake2.X86.Stream.Update.stR s₀ w).Disjoint (VG.Proof.Blake2.X86.Stream.Update.scR s₀)
  d_st : (VG.Proof.Blake2.X86.Stream.Update.dR s₀).Disjoint (VG.Proof.Blake2.X86.Stream.Update.stR s₀ w)
  d_scr : (VG.Proof.Blake2.X86.Stream.Update.dR s₀).Disjoint (VG.Proof.Blake2.X86.Stream.Update.scR s₀)
  a_st : (VG.Proof.Blake2.X86.Stream.Update.argR s₀).Disjoint (VG.Proof.Blake2.X86.Stream.Update.stR s₀ w)
  a_scr : (VG.Proof.Blake2.X86.Stream.Update.argR s₀).Disjoint (VG.Proof.Blake2.X86.Stream.Update.scR s₀)
  ret_st : (VG.Proof.Blake2.X86.Stream.Update.retR s₀).Disjoint (VG.Proof.Blake2.X86.Stream.Update.stR s₀ w)
  ret_scr : (VG.Proof.Blake2.X86.Stream.Update.retR s₀).Disjoint (VG.Proof.Blake2.X86.Stream.Update.scR s₀)
  stk_st : (VG.Proof.Blake2.X86.Stream.Update.stkR s₀).Disjoint (VG.Proof.Blake2.X86.Stream.Update.stR s₀ w)
  stk_scr : (VG.Proof.Blake2.X86.Stream.Update.stkR s₀).Disjoint (VG.Proof.Blake2.X86.Stream.Update.scR s₀)
  stk_d : (VG.Proof.Blake2.X86.Stream.Update.stkR s₀).Disjoint (VG.Proof.Blake2.X86.Stream.Update.dR s₀)
  st_fit : (VG.Proof.Blake2.X86.Stream.Update.st s₀).toNat + (bufOff w + blockBytes w) ≤ 2 ^ 32
  d_fit : (VG.Proof.Blake2.X86.Stream.Update.dp s₀).toNat + VG.Proof.Blake2.X86.Stream.Update.len s₀ ≤ 2 ^ 32
  scr_fit : (VG.Proof.Blake2.X86.Stream.Update.scr s₀).toNat + 576 ≤ 2 ^ 32
  sp_lo : 32 ≤ (VG.Proof.Blake2.X86.Stream.Update.esp₀ s₀).toNat
  sp_fit : (VG.Proof.Blake2.X86.Stream.Update.esp₀ s₀).toNat + 28 ≤ 2 ^ 32

theorem pre_of {s₀ : State} (h : (updateX86 P).pre s₀) : VG.Proof.Blake2.X86.Stream.Update.Pre w s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩ := h
  have e := VG.Proof.Blake2.X86.Stream.stk_eq h16
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, by show (below _ _).Disjoint _; rw [e]; exact h10,
    by show (below _ _).Disjoint _; rw [e]; exact h11, by show (below _ _).Disjoint _; rw [e]; exact h12,
    h13, h14, h15, h16, h17⟩

theorem len_lt (s₀ : State) : VG.Proof.Blake2.X86.Stream.Update.len s₀ < 2 ^ 32 := (VG.X86.arg s₀ 4).isLt

theorem D_length (s₀ : State) (c : Nat) : (VG.Proof.Blake2.X86.Stream.Update.D s₀ c).length = c := by simp [VG.Spec.Blake2.bytesAt]

namespace Pre
variable {s₀ : State} (hp : VG.Proof.Blake2.X86.Stream.Update.Pre w s₀)
include hp

theorem scr_in {d : Nat} (hd : d + 4 ≤ 576) : (VG.Proof.Blake2.X86.Stream.Update.scR s₀).Contains (addr (VG.Proof.Blake2.X86.Stream.Update.scr s₀) d) 4 :=
  contains_addr hd (by omega) hp.scr_fit

theorem arg_in {d : Nat} (hd₁ : 4 ≤ d) (hd : d + 4 ≤ 28) : (VG.Proof.Blake2.X86.Stream.Update.argR s₀).Contains (addr (VG.Proof.Blake2.X86.Stream.Update.esp₀ s₀) d) 4 := by
  have := hp.sp_fit
  show (⟨addr (VG.Proof.Blake2.X86.Stream.Update.esp₀ s₀) 4, 24⟩ : Region).Contains _ _
  rw [addr_eq (by omega), addr_eq (by omega)]
  exact Offset.contains _ hd₁ (by omega) (by omega)

/-- An argument word, as a region. -/
theorem arg_sub {d : Nat} (hd₁ : 4 ≤ d) (hd : d + 4 ≤ 28) : Region.Sub ⟨addr (VG.Proof.Blake2.X86.Stream.Update.esp₀ s₀) d, 4⟩ (VG.Proof.Blake2.X86.Stream.Update.argR s₀) := by
  have := hp.sp_fit
  show Region.Sub _ ⟨addr (VG.Proof.Blake2.X86.Stream.Update.esp₀ s₀) 4, 24⟩
  rw [addr_eq (by omega), addr_eq (by omega)]
  exact Offset.sub _ hd₁ (by omega)

theorem a_stk : (VG.Proof.Blake2.X86.Stream.Update.argR s₀).Disjoint (VG.Proof.Blake2.X86.Stream.Update.stkR s₀) := by
  have := hp.sp_fit; have := hp.sp_lo
  show Region.Disjoint ⟨addr (VG.Proof.Blake2.X86.Stream.Update.esp₀ s₀) 4, 24⟩ ⟨(VG.Proof.Blake2.X86.Stream.Update.esp₀ s₀ - BitVec.ofNat 32 32).setWidth 64, 32⟩
  rw [addr_eq (by omega), Taint.sub_setWidth (by omega)]
  exact Offset.disjoint_below _ (by omega)

theorem ret_stk : (VG.Proof.Blake2.X86.Stream.Update.retR s₀).Disjoint (VG.Proof.Blake2.X86.Stream.Update.stkR s₀) := by
  have := hp.sp_fit; have := hp.sp_lo
  show Region.Disjoint ⟨(VG.Proof.Blake2.X86.Stream.Update.esp₀ s₀).setWidth 64, 4⟩ ⟨(VG.Proof.Blake2.X86.Stream.Update.esp₀ s₀ - BitVec.ofNat 32 32).setWidth 64, 32⟩
  rw [Taint.sub_setWidth (by omega)]
  exact Offset.base_disjoint_below _ (by omega)

theorem rin {s : State} (hrd : s.rd = s₀.rd) {d : Nat} (h₁ : 4 ≤ d) (h₂ : d + 4 ≤ 28) :
    InRegions (s.rd ++ s.wr) (addr (VG.Proof.Blake2.X86.Stream.Update.esp₀ s₀) d) 4 :=
  ⟨VG.Proof.Blake2.X86.Stream.Update.argR s₀, by simp [hrd, hp.rd], hp.arg_in h₁ h₂⟩

theorem sin {s : State} (hwr : s.wr = s₀.wr) {d : Nat} (hd : d + 4 ≤ 576) :
    InRegions s.wr (addr (VG.Proof.Blake2.X86.Stream.Update.scr s₀) d) 4 :=
  ⟨VG.Proof.Blake2.X86.Stream.Update.scR s₀, by simp [hwr, hp.wr], hp.scr_in hd⟩

theorem sinr {s : State} (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) {d : Nat} (hd : d + 4 ≤ 576) :
    InRegions (s.rd ++ s.wr) (addr (VG.Proof.Blake2.X86.Stream.Update.scr s₀) d) 4 :=
  ⟨VG.Proof.Blake2.X86.Stream.Update.scR s₀, by simp [hrd, hwr, hp.wr], hp.scr_in hd⟩

/-- The scratch space is disjoint from the other regions the code writes. -/
theorem scr_disj : ∀ r ∈ [VG.Proof.Blake2.X86.Stream.Update.stR s₀ w, VG.Proof.Blake2.X86.Stream.Update.stkR s₀], Region.Disjoint ⟨(VG.Proof.Blake2.X86.Stream.Update.scr s₀).setWidth 64, 576⟩ r := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨hp.st_scr.symm, hp.stk_scr.symm⟩

end Pre

/-- The data the initial state represents, from `h0`. -/
def R₀ (P : VG.Spec.Blake2.Params w) (s₀ : State) (h0 : VG.Spec.Blake2.HashValue w) (d : List Byte) : Prop :=
  Spec.Blake2.Repr P h0 s₀.mem (VG.Proof.Blake2.X86.Stream.Update.stA s₀) d ∧ countX86 s₀ = BitVec.ofNat 64 d.length ∧
    d.length + VG.Proof.Blake2.X86.Stream.Update.len s₀ < 2 ^ 64

theorem R₀.cnt_eq {s₀ : State} {h0 : VG.Spec.Blake2.HashValue w} {d : List Byte} (h : VG.Proof.Blake2.X86.Stream.Update.R₀ P s₀ h0 d) :
    VG.Proof.Blake2.X86.Stream.Update.cnt s₀ = d.length := by
  rw [VG.Proof.Blake2.X86.Stream.Update.cnt, h.2.1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := h.2.2; omega)]

/-! ## Invariants -/

/-- What holds throughout, after consuming `c` bytes of data. -/
structure Common (w : Nat) (s₀ : State) (c : Nat) (s : State) : Prop where
  c_le : c ≤ VG.Proof.Blake2.X86.Stream.Update.len s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  ebx : s.gpr .ebx = VG.Proof.Blake2.X86.Stream.Update.st s₀
  ebp : s.gpr .ebp = VG.Proof.Blake2.X86.Stream.Update.scr s₀
  esp : s.gpr .esp = VG.Proof.Blake2.X86.Stream.Update.esp₀ s₀
  frame : Frame [VG.Proof.Blake2.X86.Stream.Update.stR s₀ w, VG.Proof.Blake2.X86.Stream.Update.scR s₀, VG.Proof.Blake2.X86.Stream.Update.stkR s₀] s₀.mem s.mem
  saved : VG.Proof.Blake2.X86.Stream.Saved (VG.Proof.Blake2.X86.Stream.Update.scr s₀) s₀ s.mem

/-- The state represents the data followed by the first `c` bytes of data,
the last `r` of them in the buffer. -/
structure Inv (P : VG.Spec.Blake2.Params w) (s₀ : State) (c r : Nat) (s : State) : Prop extends VG.Proof.Blake2.X86.Stream.Update.Common w s₀ c s where
  repr : ∀ h0 d, VG.Proof.Blake2.X86.Stream.Update.R₀ P s₀ h0 d → ReprR P h0 s.mem (VG.Proof.Blake2.X86.Stream.Update.stA s₀) (d ++ VG.Proof.Blake2.X86.Stream.Update.D s₀ c) r

/-- The data pointer and the bytes left. -/
structure Ptr (s₀ : State) (c : Nat) (s : State) : Prop where
  esi : s.gpr .esi = VG.Proof.Blake2.X86.Stream.Update.dp s₀ + BitVec.ofNat 32 c
  edi : s.gpr .edi = BitVec.ofNat 32 (VG.Proof.Blake2.X86.Stream.Update.len s₀ - c)

/-- The byte count. -/
structure Cnt (s₀ : State) (c : Nat) (m : Mem) : Prop where
  lo : m.readW (addr (VG.Proof.Blake2.X86.Stream.Update.scr s₀) cloOff) 32 = BitVec.ofNat 32 (VG.Proof.Blake2.X86.Stream.Update.cnt s₀ + c)
  hi : m.readW (addr (VG.Proof.Blake2.X86.Stream.Update.scr s₀) chiOff) 32 = BitVec.ofNat 32 ((VG.Proof.Blake2.X86.Stream.Update.cnt s₀ + c) / 2 ^ 32)

theorem Common.of_gpr {s₀ : State} {c : Nat} {s s' : State} (h : VG.Proof.Blake2.X86.Stream.Update.Common w s₀ c s)
    (hg : ∀ r ∈ [Reg.ebx, .ebp, .esp], s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : VG.Proof.Blake2.X86.Stream.Update.Common w s₀ c s' where
  c_le := h.c_le
  rd := hrd.trans h.rd
  wr := hwr.trans h.wr
  ebx := by rw [hg _ (by simp)]; exact h.ebx
  ebp := by rw [hg _ (by simp)]; exact h.ebp
  esp := by rw [hg _ (by simp)]; exact h.esp
  frame := by rw [hm]; exact h.frame
  saved := by rw [hm]; exact h.saved

theorem Inv.of_gpr {s₀ : State} {c r : Nat} {s s' : State} (h : VG.Proof.Blake2.X86.Stream.Update.Inv P s₀ c r s)
    (hg : ∀ r ∈ [Reg.ebx, .ebp, .esp], s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : VG.Proof.Blake2.X86.Stream.Update.Inv P s₀ c r s' :=
  { h.toCommon.of_gpr hg hm hrd hwr with repr := by rw [hm]; exact h.repr }

theorem Ptr.of_gpr {s₀ : State} {c : Nat} {s s' : State} (h : VG.Proof.Blake2.X86.Stream.Update.Ptr s₀ c s)
    (h₁ : s'.gpr .esi = s.gpr .esi) (h₂ : s'.gpr .edi = s.gpr .edi) : VG.Proof.Blake2.X86.Stream.Update.Ptr s₀ c s' :=
  ⟨h₁.trans h.esi, h₂.trans h.edi⟩

/-- The argument words are never written. -/
theorem Common.arg {s₀ : State} (hp : VG.Proof.Blake2.X86.Stream.Update.Pre w s₀) {c : Nat} {s : State} (h : VG.Proof.Blake2.X86.Stream.Update.Common w s₀ c s) {d : Nat}
    (h₁ : 4 ≤ d) (h₂ : d + 4 ≤ 28) :
    s.mem.readW (addr (VG.Proof.Blake2.X86.Stream.Update.esp₀ s₀) d) 32 = s₀.mem.readW (addr (VG.Proof.Blake2.X86.Stream.Update.esp₀ s₀) d) 32 := by
  refine h.frame.readW (r := ⟨addr (VG.Proof.Blake2.X86.Stream.Update.esp₀ s₀) d, 4⟩) (Region.contains_self _ _) ?_ (by decide)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hp.a_st.sub_left (hp.arg_sub h₁ h₂)
  · exact hp.a_scr.sub_left (hp.arg_sub h₁ h₂)
  · exact hp.a_stk.sub_left (hp.arg_sub h₁ h₂)

/-- The data is unchanged. -/
theorem Common.data {s₀ : State} (hp : VG.Proof.Blake2.X86.Stream.Update.Pre w s₀) {c : Nat} {s : State} (h : VG.Proof.Blake2.X86.Stream.Update.Common w s₀ c s) {i : Nat}
    (hi : i < VG.Proof.Blake2.X86.Stream.Update.len s₀) : s.mem (VG.Proof.Blake2.X86.Stream.Update.dA s₀ + BitVec.ofNat 64 i) = s₀.mem (VG.Proof.Blake2.X86.Stream.Update.dA s₀ + BitVec.ofNat 64 i) :=
  h.frame.bytes (R := VG.Proof.Blake2.X86.Stream.Update.dR s₀) (by simpa using ⟨hp.d_st, hp.d_scr, hp.stk_d.symm⟩)
    (by have := VG.Proof.Blake2.X86.Stream.Update.len_lt s₀; simp only; omega) hi

/-- Writes to the scratch space keep the state's bytes. -/
theorem st_keep (hP : VG.Proof.Blake2.X86.Stream.Ok P) {s₀ : State} (hp : VG.Proof.Blake2.X86.Stream.Update.Pre w s₀) {m m' : Mem} (hf : Frame [VG.Proof.Blake2.X86.Stream.Update.scR s₀] m m') :
    ∀ i < bufOff w + blockBytes w, m' (VG.Proof.Blake2.X86.Stream.Update.stA s₀ + BitVec.ofNat 64 i) = m (VG.Proof.Blake2.X86.Stream.Update.stA s₀ + BitVec.ofNat 64 i) :=
  fun i hi => hf.bytes (R := VG.Proof.Blake2.X86.Stream.Update.stR s₀ w) (by simpa using hp.st_scr) (by have := hP.len; simp only; omega) hi

/-! ## Prologue -/

/-- The memory after the prologue. -/
def proMem (s₀ : State) : Mem :=
  ((VG.Proof.Blake2.X86.Stream.saveMem (VG.Proof.Blake2.X86.Stream.Update.scr s₀) s₀).writeW (addr (VG.Proof.Blake2.X86.Stream.Update.scr s₀) cloOff) (VG.X86.arg s₀ 1)).writeW (addr (VG.Proof.Blake2.X86.Stream.Update.scr s₀) chiOff) (VG.X86.arg s₀ 2)

theorem proMem_frame {s₀ : State} (hp : VG.Proof.Blake2.X86.Stream.Update.Pre w s₀) : Frame [VG.Proof.Blake2.X86.Stream.Update.scR s₀] s₀.mem (VG.Proof.Blake2.X86.Stream.Update.proMem s₀) :=
  ((VG.Proof.Blake2.X86.Stream.saveMem_frame hp.scr_fit s₀).writeW (List.mem_singleton_self _) _ (hp.scr_in (by decide))).writeW
    (List.mem_singleton_self _) _ (hp.scr_in (by decide))

theorem cnt_lo (s₀ : State) : BitVec.ofNat 32 (VG.Proof.Blake2.X86.Stream.Update.cnt s₀) = VG.X86.arg s₀ 1 := VG.Proof.Blake2.X86.Stream.lo_append _ _
theorem cnt_hi (s₀ : State) : BitVec.ofNat 32 (VG.Proof.Blake2.X86.Stream.Update.cnt s₀ / 2 ^ 32) = VG.X86.arg s₀ 2 := VG.Proof.Blake2.X86.Stream.hi_append _ _

theorem proMem_cnt {s₀ : State} (hp : VG.Proof.Blake2.X86.Stream.Update.Pre w s₀) : VG.Proof.Blake2.X86.Stream.Update.Cnt s₀ 0 (VG.Proof.Blake2.X86.Stream.Update.proMem s₀) := by
  refine ⟨?_, ?_⟩ <;> simp only [VG.Proof.Blake2.X86.Stream.Update.proMem, Nat.add_zero]
  · rw [VG.Proof.Blake2.X86.Stream.rw_scr hp.scr_fit _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32, VG.Proof.Blake2.X86.Stream.Update.cnt_lo]
  · rw [Mem.readW_writeW_self32, VG.Proof.Blake2.X86.Stream.Update.cnt_hi]

theorem proMem_saved {s₀ : State} (hp : VG.Proof.Blake2.X86.Stream.Update.Pre w s₀) : VG.Proof.Blake2.X86.Stream.Saved (VG.Proof.Blake2.X86.Stream.Update.scr s₀) s₀ (VG.Proof.Blake2.X86.Stream.Update.proMem s₀) :=
  (VG.Proof.Blake2.X86.Stream.saveMem_saved hp.scr_fit s₀).of_readW fun p hp' => by
    have := VG.Proof.Blake2.X86.Stream.saved_bound p hp'
    simp only [VG.Proof.Blake2.X86.Stream.Update.proMem]
    rw [VG.Proof.Blake2.X86.Stream.rw_scr hp.scr_fit _ _ (by omega) (by decide) (by simp only [chiOff]; omega),
      VG.Proof.Blake2.X86.Stream.rw_scr hp.scr_fit _ _ (by omega) (by decide) (by simp only [cloOff]; omega)]

theorem prologue_ok {s₀ : State} (hp : VG.Proof.Blake2.X86.Stream.Update.Pre w s₀) :
    WP isa (.block updateStart) s₀ fun s =>
      VG.Proof.Blake2.X86.Stream.Update.Common w s₀ 0 s ∧ VG.Proof.Blake2.X86.Stream.Update.Ptr s₀ 0 s ∧ s.mem = VG.Proof.Blake2.X86.Stream.Update.proMem s₀ ∧ s.gpr .eax = VG.X86.arg s₀ 1 ∧ s.gpr .ecx = VG.X86.arg s₀ 2 := by
  have rin : ∀ {d}, 4 ≤ d → d + 4 ≤ 28 → InRegions (s₀.rd ++ s₀.wr) (addr (VG.Proof.Blake2.X86.Stream.Update.esp₀ s₀) d) 4 :=
    fun h₁ h₂ => hp.rin rfl h₁ h₂
  have sin : ∀ {d}, d + 4 ≤ 576 → InRegions s₀.wr (addr (VG.Proof.Blake2.X86.Stream.Update.scr s₀) d) 4 := fun h => hp.sin rfl h
  -- The saves only touch the scratch space, so the arguments stay readable.
  have sepA : ∀ d e, 512 ≤ d → d + 4 ≤ 576 → 4 ≤ e → e + 4 ≤ 28 →
      Mem.Sep (addr (VG.Proof.Blake2.X86.Stream.Update.esp₀ s₀) e) 4 (addr (VG.Proof.Blake2.X86.Stream.Update.scr s₀) d) 4 := by
    intro d e h₁ h₂ h₃ h₄
    exact hp.a_scr.sep (hp.arg_in h₃ h₄) (hp.scr_in h₂)
  have argSave : ∀ e, 4 ≤ e → e + 4 ≤ 28 →
      (VG.Proof.Blake2.X86.Stream.saveMem (VG.Proof.Blake2.X86.Stream.Update.scr s₀) s₀).readW (addr (VG.Proof.Blake2.X86.Stream.Update.esp₀ s₀) e) 32 = s₀.mem.readW (addr (VG.Proof.Blake2.X86.Stream.Update.esp₀ s₀) e) 32 := by
    intro e h₁ h₂
    exact Spill.saveMem_readW_of_sep _ _ (by decide) _ _ fun p h =>
      have := VG.Proof.Blake2.X86.Stream.saved_bound p h; sepA _ e this.1 (by omega) h₁ h₂
  rw [show updateStart = .mov .eax (.mem (at_ .esp 24)) :: (Spill.saveCode .eax saved ++
    ([.mov .ebp (.reg .eax), .mov .ebx (.mem (at_ .esp 4)), .mov .esi (.mem (at_ .esp 16)),
      .mov .edi (.mem (at_ .esp 20)), .mov .eax (.mem (at_ .esp 8)), .store (at_ .ebp cloOff) .eax,
      .mov .ecx (.mem (at_ .esp 12)), .store (at_ .ebp chiOff) .ecx] : List Instr)) from rfl]
  refine wp_ldm (B := VG.Proof.Blake2.X86.Stream.Update.esp₀ s₀) rfl (rin (d := 24) (by omega) (by omega)) fun s₁ u₁ => ?_
  have e₁ : s₁.gpr .eax = VG.Proof.Blake2.X86.Stream.Update.scr s₀ := u₁.gpr
  refine Spill.save_ok saved (fun p h => by
    rw [e₁, u₁.wr]; exact sin (by have := VG.Proof.Blake2.X86.Stream.saved_bound p h; omega)) fun s₅ u₅ => ?_
  have g₅ : s₅.gpr = s₁.gpr := u₅.gpr
  have m₅ : s₅.mem = VG.Proof.Blake2.X86.Stream.saveMem (VG.Proof.Blake2.X86.Stream.Update.scr s₀) s₀ := by
    rw [u₅.mem, e₁, u₁.mem]
    exact Spill.saveMem_congr _ _ (fun _ _ => rfl) fun p h => u₁.other _ (by revert p h; decide)
  have rd₅ : s₅.rd = s₀.rd := by rw [u₅.rd, u₁.rd]
  have wr₅ : s₅.wr = s₀.wr := by rw [u₅.wr, u₁.wr]
  have sp₅ : s₅.gpr .esp = VG.Proof.Blake2.X86.Stream.Update.esp₀ s₀ := by rw [g₅, u₁.other _ (by decide)]
  have ld : ∀ e, 4 ≤ e → e + 4 ≤ 28 → s₅.mem.readW (addr (VG.Proof.Blake2.X86.Stream.Update.esp₀ s₀) e) 32 = s₀.mem.readW (addr (VG.Proof.Blake2.X86.Stream.Update.esp₀ s₀) e) 32 :=
    fun e h₁ h₂ => by rw [m₅]; exact argSave e h₁ h₂
  refine wp_mov fun s₆ u₆ => ?_
  have ebp₆ : s₆.gpr .ebp = VG.Proof.Blake2.X86.Stream.Update.scr s₀ := by rw [u₆.gpr, g₅, e₁]
  have sp₆ : s₆.gpr .esp = VG.Proof.Blake2.X86.Stream.Update.esp₀ s₀ := by rw [u₆.other _ (by decide), sp₅]
  have rd' : ∀ d, 4 ≤ d → d + 4 ≤ 28 → InRegions (s₆.rd ++ s₆.wr) (addr (VG.Proof.Blake2.X86.Stream.Update.esp₀ s₀) d) 4 :=
    fun d h₁ h₂ => by rw [u₆.rd, u₆.wr, rd₅, wr₅]; exact rin h₁ h₂
  refine wp_ldm sp₆ (rd' 4 (by omega) (by omega)) fun s₇ u₇ => ?_
  refine wp_ldm (by rw [u₇.other _ (by decide), sp₆]) (by rw [u₇.rd, u₇.wr]; exact rd' 16 (by omega) (by omega))
    fun s₈ u₈ => ?_
  refine wp_ldm (by rw [u₈.other _ (by decide), u₇.other _ (by decide), sp₆])
    (by rw [u₈.rd, u₈.wr, u₇.rd, u₇.wr]; exact rd' 20 (by omega) (by omega)) fun s₉ u₉ => ?_
  refine wp_ldm (by rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), sp₆])
    (by rw [u₉.rd, u₉.wr, u₈.rd, u₈.wr, u₇.rd, u₇.wr]; exact rd' 8 (by omega) (by omega)) fun s₁₀ u₁₀ => ?_
  have g₁₀ : ∀ r, r ≠ .eax → r ≠ .edi → r ≠ .esi → r ≠ .ebx → s₁₀.gpr r = s₆.gpr r := fun r a b c d => by
    rw [u₁₀.other r a, u₉.other r b, u₈.other r c, u₇.other r d]
  have m₁₀ : s₁₀.mem = VG.Proof.Blake2.X86.Stream.saveMem (VG.Proof.Blake2.X86.Stream.Update.scr s₀) s₀ := by rw [u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, m₅]
  have rd₁₀ : s₁₀.rd = s₀.rd := by rw [u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, rd₅]
  have wr₁₀ : s₁₀.wr = s₀.wr := by rw [u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, wr₅]
  refine wp_stm (by rw [g₁₀ _ (by decide) (by decide) (by decide) (by decide), ebp₆])
    (hp.sin wr₁₀ (d := cloOff) (by decide)) fun s₁₁ u₁₁ => ?_
  refine wp_ldm (by rw [u₁₁.gpr, g₁₀ _ (by decide) (by decide) (by decide) (by decide), sp₆])
    (by rw [u₁₁.rd, u₁₁.wr]; exact hp.rin rd₁₀ (d := 12) (by omega) (by omega)) fun s₁₂ u₁₂ => ?_
  refine wp_stm (by rw [u₁₂.other _ (by decide), u₁₁.gpr, g₁₀ _ (by decide) (by decide) (by decide) (by decide),
    ebp₆]) (by rw [u₁₂.wr, u₁₁.wr]; exact hp.sin wr₁₀ (d := chiOff) (by decide)) fun s₁₃ u₁₃ => WP.block_nil ?_
  -- The argument words the loads read.
  have a8 : s₁₀.gpr .eax = VG.X86.arg s₀ 1 := by
    rw [u₁₀.gpr, u₉.mem, u₈.mem, u₇.mem, u₆.mem, ld 8 (by omega) (by omega)]; rfl
  have a12 : s₁₂.gpr .ecx = VG.X86.arg s₀ 2 := by
    rw [u₁₂.gpr, u₁₁.mem, m₁₀, Mem.readW_writeW_sep (sepA cloOff 12 (by decide) (by decide) (by omega)
      (by omega)) (by decide), argSave 12 (by omega) (by omega)]; rfl
  have g₁₃ : ∀ r, r ≠ .ecx → s₁₃.gpr r = s₁₀.gpr r := fun r h => by
    rw [u₁₃.gpr, u₁₂.other r h, u₁₁.gpr]
  have m₁₃ : s₁₃.mem = VG.Proof.Blake2.X86.Stream.Update.proMem s₀ := by
    rw [u₁₃.mem, a12, u₁₂.mem, u₁₁.mem, a8, m₁₀]; rfl
  have rd₁₃ : s₁₃.rd = s₀.rd := by rw [u₁₃.rd, u₁₂.rd, u₁₁.rd, rd₁₀]
  have wr₁₃ : s₁₃.wr = s₀.wr := by rw [u₁₃.wr, u₁₂.wr, u₁₁.wr, wr₁₀]
  have l4 : s₆.mem.readW (addr (VG.Proof.Blake2.X86.Stream.Update.esp₀ s₀) 4) 32 = VG.X86.arg s₀ 0 := by rw [u₆.mem, ld 4 (by omega) (by omega)]; rfl
  have l16 : s₆.mem.readW (addr (VG.Proof.Blake2.X86.Stream.Update.esp₀ s₀) 16) 32 = VG.X86.arg s₀ 3 := by
    rw [u₆.mem, ld 16 (by omega) (by omega)]; rfl
  have l20 : s₆.mem.readW (addr (VG.Proof.Blake2.X86.Stream.Update.esp₀ s₀) 20) 32 = VG.X86.arg s₀ 4 := by
    rw [u₆.mem, ld 20 (by omega) (by omega)]; rfl
  refine ⟨⟨Nat.zero_le _, rd₁₃, wr₁₃, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_⟩, m₁₃, ?_, ?_⟩
  · rw [g₁₃ _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr, l4]
  · rw [g₁₃ _ (by decide), g₁₀ _ (by decide) (by decide) (by decide) (by decide), ebp₆]
  · rw [g₁₃ _ (by decide), g₁₀ _ (by decide) (by decide) (by decide) (by decide), sp₆]
  · rw [m₁₃]; exact (VG.Proof.Blake2.X86.Stream.Update.proMem_frame hp).mono (by simp)
  · rw [m₁₃]; exact VG.Proof.Blake2.X86.Stream.Update.proMem_saved hp
  · rw [g₁₃ _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.gpr, u₇.mem, l16]; simp
  · rw [g₁₃ _ (by decide), u₁₀.other _ (by decide), u₉.gpr, u₈.mem, u₇.mem, l20]; simp
  · rw [g₁₃ _ (by decide), a8]
  · rw [u₁₃.gpr, a12]

/-! ## The bytes in the buffer -/

theorem bufLen_ok (hP : VG.Proof.Blake2.X86.Stream.Ok P) {s₀ : State} (hp : VG.Proof.Blake2.X86.Stream.Update.Pre w s₀) {s : State} (hC : VG.Proof.Blake2.X86.Stream.Update.Common w s₀ 0 s)
    (hptr : VG.Proof.Blake2.X86.Stream.Update.Ptr s₀ 0 s) (hm : s.mem = VG.Proof.Blake2.X86.Stream.Update.proMem s₀) (hax : s.gpr .eax = VG.X86.arg s₀ 1) (hcx : s.gpr .ecx = VG.X86.arg s₀ 2) :
    WP isa (Impl.Blake2.X86.Stream.bufLen w) s fun s' =>
      VG.Proof.Blake2.X86.Stream.Update.Inv P s₀ 0 (Proof.Blake2.bufLen w (VG.Proof.Blake2.X86.Stream.Update.cnt s₀)) s' ∧ VG.Proof.Blake2.X86.Stream.Update.Ptr s₀ 0 s' ∧ VG.Proof.Blake2.X86.Stream.Update.Cnt s₀ 0 s'.mem ∧
        s'.gpr .eax = BitVec.ofNat 32 (Proof.Blake2.bufLen w (VG.Proof.Blake2.X86.Stream.Update.cnt s₀)) := by
  -- The representation.
  have hrepr : ∀ h0 d, VG.Proof.Blake2.X86.Stream.Update.R₀ P s₀ h0 d →
      ReprR P h0 s.mem (VG.Proof.Blake2.X86.Stream.Update.stA s₀) (d ++ VG.Proof.Blake2.X86.Stream.Update.D s₀ 0) (Proof.Blake2.bufLen w (VG.Proof.Blake2.X86.Stream.Update.cnt s₀)) := by
    intro h0 d hd
    have e : VG.Proof.Blake2.X86.Stream.Update.D s₀ 0 = [] := by simp [VG.Spec.Blake2.bytesAt]
    rw [e, List.append_nil, hd.cnt_eq, ← repr_iff P hP.pos, hm]
    exact VG.Proof.Blake2.X86.Stream.repr_congr hP (VG.Proof.Blake2.X86.Stream.Update.st_keep hP hp (VG.Proof.Blake2.X86.Stream.Update.proMem_frame hp)) hd.1
  have hcnt := VG.Proof.Blake2.X86.Stream.Update.proMem_cnt hp
  rw [← hm] at hcnt
  unfold Impl.Blake2.X86.Stream.bufLen
  refine WP.seq (VG.Proof.Blake2.X86.Stream.wp_orZ fun s₁ u₁ z₁ => WP.block_nil ?_)
  have hz : isa.eval .e s₁ = some (decide (VG.Proof.Blake2.X86.Stream.Update.cnt s₀ = 0)) := by
    show s₁.zf = _
    rw [z₁, hcx, hax, VG.Proof.Blake2.X86.Stream.or_beq_zero]; rfl
  have hC₁ : VG.Proof.Blake2.X86.Stream.Update.Common w s₀ 0 s₁ := hC.of_gpr (fun r hr => u₁.other r (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide))
    u₁.mem u₁.rd u₁.wr
  have hptr₁ : VG.Proof.Blake2.X86.Stream.Update.Ptr s₀ 0 s₁ := hptr.of_gpr (u₁.other _ (by decide)) (u₁.other _ (by decide))
  refine WP.ite _ hz (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    refine wp_movi fun s₂ u₂ => WP.block_nil ?_
    have e : Proof.Blake2.bufLen w (VG.Proof.Blake2.X86.Stream.Update.cnt s₀) = 0 := by simp [Proof.Blake2.bufLen, hb]
    refine ⟨{ hC₁.of_gpr (fun r hr => u₂.other r (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide))
      u₂.mem u₂.rd u₂.wr with repr := ?_ }, hptr₁.of_gpr (u₂.other _ (by decide)) (u₂.other _ (by decide)),
      by rw [u₂.mem, u₁.mem]; exact hcnt, by rw [u₂.gpr, e]; rfl⟩
    rw [u₂.mem, u₁.mem]; exact hrepr
  · simp only [decide_eq_false_iff_not] at hb
    refine wp_subi fun s₂ u₂ _ _ => wp_andi fun s₃ u₃ => wp_addi fun s₄ u₄ => WP.block_nil ?_
    have g : ∀ r, r ≠ .eax → s₄.gpr r = s₁.gpr r := fun r h => by
      rw [u₄.other r h, u₃.other r h, u₂.other r h]
    have hm₄ : s₄.mem = s.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
    refine ⟨{ hC₁.of_gpr (fun r hr => g r (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide))
      (by rw [hm₄, u₁.mem]) (by rw [u₄.rd, u₃.rd, u₂.rd]) (by rw [u₄.wr, u₃.wr, u₂.wr]) with repr := ?_ },
      hptr₁.of_gpr (g _ (by decide)) (g _ (by decide)), by rw [hm₄]; exact hcnt, ?_⟩
    · rw [hm₄]; exact hrepr
    · rw [u₄.gpr, u₃.gpr, u₂.gpr, u₁.other _ (by decide), hax, ← VG.Proof.Blake2.X86.Stream.Update.cnt_lo, VG.Proof.Blake2.X86.Stream.mask_ofNat hP hb]
      simp [Proof.Blake2.bufLen, hb]

/-! ## Copying data into the buffer -/

theorem dp_add {s₀ : State} (hp : VG.Proof.Blake2.X86.Stream.Update.Pre w s₀) {c : Nat} (hc : c < VG.Proof.Blake2.X86.Stream.Update.len s₀) :
    (VG.Proof.Blake2.X86.Stream.Update.dp s₀ + BitVec.ofNat 32 c).setWidth 64 = VG.Proof.Blake2.X86.Stream.Update.dA s₀ + BitVec.ofNat 64 c :=
  VG.Proof.Blake2.X86.Stream.sw_add (by have := hp.d_fit; omega)

/-- Copying `k` bytes of data, from byte `c` on, into the buffer, from byte
`r` on: only the buffer changes. -/
theorem copy_ok (hP : VG.Proof.Blake2.X86.Stream.Ok P) {s₀ : State} (hp : VG.Proof.Blake2.X86.Stream.Update.Pre w s₀) {c r k : Nat} (hk : 1 ≤ k)
    (hrk : r + k ≤ blockBytes w) (hck : c + k ≤ VG.Proof.Blake2.X86.Stream.Update.len s₀) {s : State}
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (hesi : s.gpr .esi = VG.Proof.Blake2.X86.Stream.Update.dp s₀ + BitVec.ofNat 32 c)
    (hedx : s.gpr .edx = VG.Proof.Blake2.X86.Stream.Update.st s₀ + BitVec.ofNat 32 r) (hecx : s.gpr .ecx = BitVec.ofNat 32 k)
    (hf : Frame [VG.Proof.Blake2.X86.Stream.Update.stR s₀ w, VG.Proof.Blake2.X86.Stream.Update.scR s₀, VG.Proof.Blake2.X86.Stream.Update.stkR s₀] s₀.mem s.mem)
    (hrepr : ∀ h0 d, VG.Proof.Blake2.X86.Stream.Update.R₀ P s₀ h0 d → ReprR P h0 s.mem (VG.Proof.Blake2.X86.Stream.Update.stA s₀) (d ++ VG.Proof.Blake2.X86.Stream.Update.D s₀ c) r) :
    WP isa (copyLoop w .esi .edx .ecx .al) s fun s' =>
      (∀ x, x ≠ .esi → x ≠ .edx → x ≠ .ecx → x ≠ .eax → s'.gpr x = s.gpr x) ∧
      s'.gpr .esi = VG.Proof.Blake2.X86.Stream.Update.dp s₀ + BitVec.ofNat 32 (c + k) ∧ s'.rd = s₀.rd ∧ s'.wr = s₀.wr ∧
      Frame [VG.Proof.Blake2.X86.Stream.Update.stR s₀ w] s.mem s'.mem ∧
      ∀ h0 d, VG.Proof.Blake2.X86.Stream.Update.R₀ P s₀ h0 d → ReprR P h0 s'.mem (VG.Proof.Blake2.X86.Stream.Update.stA s₀) (d ++ VG.Proof.Blake2.X86.Stream.Update.D s₀ (c + k)) (r + k) := by
  have hl := hP.len
  have hL := VG.Proof.Blake2.X86.Stream.Update.len_lt s₀
  have fS := hp.st_fit
  have fD := hp.d_fit
  have hN : bufOff w = blockBytes w / 2 := hP.N
  have eD : addr (VG.Proof.Blake2.X86.Stream.Update.st s₀ + BitVec.ofNat 32 r) (bufOff w) = VG.Proof.Blake2.X86.Stream.Update.stA s₀ + BitVec.ofNat 64 (bufOff w + r) := by
    rw [MdStream.X86.addr_add_ofNat (by omega), Nat.add_comm]
  have eS : (VG.Proof.Blake2.X86.Stream.Update.dp s₀ + BitVec.ofNat 32 c).setWidth 64 = VG.Proof.Blake2.X86.Stream.Update.dA s₀ + BitVec.ofNat 64 c := VG.Proof.Blake2.X86.Stream.Update.dp_add hp (by omega)
  have hsrc : ∀ i < k, InRegions (s.rd ++ s.wr) ((VG.Proof.Blake2.X86.Stream.Update.dp s₀ + BitVec.ofNat 32 c).setWidth 64 + BitVec.ofNat 64 i) 1 :=
    fun i hi => ⟨VG.Proof.Blake2.X86.Stream.Update.dR s₀, by simp [hrd, hp.rd], by
      rw [eS, Offset.add_add]; exact contains_offset (by omega) (by omega)⟩
  have hdst : ∀ i < k, InRegions s.wr (addr (VG.Proof.Blake2.X86.Stream.Update.st s₀ + BitVec.ofNat 32 r) (bufOff w) + BitVec.ofNat 64 i) 1 :=
    fun i hi => ⟨VG.Proof.Blake2.X86.Stream.Update.stR s₀ w, by simp [hwr, hp.wr], by
      rw [eD, Offset.add_add]; exact contains_offset (by omega) (by omega)⟩
  have hd : Region.Disjoint ⟨(VG.Proof.Blake2.X86.Stream.Update.dp s₀ + BitVec.ofNat 32 c).setWidth 64, k⟩
      ⟨addr (VG.Proof.Blake2.X86.Stream.Update.st s₀ + BitVec.ofNat 32 r) (bufOff w), k⟩ := by
    rw [eS, eD]
    exact (hp.d_st.sub_left (sub_offset (by omega) (by omega))).sub_right (sub_offset (by omega) (by omega))
  refine VG.Proof.Blake2.X86.Stream.copyLoop_ok (w := w) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hk
    (by omega) (by rw [VG.Proof.Blake2.X86.Stream.toNat_add_ofNat (by omega)]; omega) (by rw [VG.Proof.Blake2.X86.Stream.toNat_add_ofNat (by omega)]; omega)
    hesi hedx hecx hsrc hdst hd fun s' h => ?_
  -- The bytes copied.
  have hx : VG.Spec.Blake2.bytesAt s.mem ((VG.Proof.Blake2.X86.Stream.Update.dp s₀ + BitVec.ofNat 32 c).setWidth 64) k =
      VG.Spec.Blake2.bytesAt s₀.mem (VG.Proof.Blake2.X86.Stream.Update.dA s₀ + BitVec.ofNat 64 c) k := by
    rw [eS]
    refine bytesAt_congr fun i hi => ?_
    rw [Offset.add_add]
    exact hf.bytes (R := VG.Proof.Blake2.X86.Stream.Update.dR s₀) (by simpa using ⟨hp.d_st, hp.d_scr, hp.stk_d.symm⟩)
      (by simp only; omega) (show c + i < VG.Proof.Blake2.X86.Stream.Update.len s₀ by omega)
  have hm : s'.mem = VG.WriteBytes.writeBytes s.mem (VG.Proof.Blake2.X86.Stream.Update.stA s₀ + BitVec.ofNat 64 (bufOff w + r))
      (VG.Spec.Blake2.bytesAt s₀.mem (VG.Proof.Blake2.X86.Stream.Update.dA s₀ + BitVec.ofNat 64 c) k) := by
    rw [h.mem, List.take_of_length_le (by rw [VG.Proof.Blake2.X86.Stream.bytesAt_length]), hx, eD]
  have hfw : Frame [VG.Proof.Blake2.X86.Stream.Update.stR s₀ w] s.mem s'.mem := by
    rw [hm]; exact VG.WriteBytes.writeBytes_frame _ _ _ (by rw [VG.Proof.Blake2.X86.Stream.bytesAt_length]; exact contains_offset (by omega) (by omega))
  refine ⟨fun x a b c d => h.other x a b c d, ?_, h.rd.trans hrd, h.wr.trans hwr, hfw, fun h0 d hd => ?_⟩
  · rw [h.srcV, BitVec.add_assoc, BitVec.ofNat_add]
  have e : d ++ VG.Proof.Blake2.X86.Stream.Update.D s₀ (c + k) = d ++ VG.Proof.Blake2.X86.Stream.Update.D s₀ c ++ VG.Spec.Blake2.bytesAt s₀.mem (VG.Proof.Blake2.X86.Stream.Update.dA s₀ + BitVec.ofNat 64 c) k := by
    rw [VG.Proof.Blake2.X86.Stream.Update.D, bytesAt_add, List.append_assoc]
  rw [e]
  have := reprR_append P (hrepr h0 d hd) (x := VG.Spec.Blake2.bytesAt s₀.mem (VG.Proof.Blake2.X86.Stream.Update.dA s₀ + BitVec.ofNat 64 c) k)
    (mem' := s'.mem) (by rw [VG.Proof.Blake2.X86.Stream.bytesAt_length]; exact hrk) ?_ ?_
  · rwa [VG.Proof.Blake2.X86.Stream.bytesAt_length] at this
  · rw [hm]
    exact stateAt_congr fun i hi => VG.WriteBytes.writeBytes_before _ _ _ (by omega)
      (by rw [VG.Proof.Blake2.X86.Stream.bytesAt_length]; omega)
  · rw [hm, ← Offset.add_add, VG.Proof.Blake2.X86.Stream.bytesAt_writeBytes _ _ _ _ (by rw [VG.Proof.Blake2.X86.Stream.bytesAt_length]; omega)]

/-! ## Writes to the scratch space and the buffer -/

theorem Saved.write {s₀ : State} (hp : VG.Proof.Blake2.X86.Stream.Update.Pre w s₀) {m : Mem} (h : VG.Proof.Blake2.X86.Stream.Saved (VG.Proof.Blake2.X86.Stream.Update.scr s₀) s₀ m) {d : Nat} (hd : 528 ≤ d)
    (hd' : d + 4 ≤ 576) (v : BitVec 32) : VG.Proof.Blake2.X86.Stream.Saved (VG.Proof.Blake2.X86.Stream.Update.scr s₀) s₀ (m.writeW (addr (VG.Proof.Blake2.X86.Stream.Update.scr s₀) d) v) :=
  h.of_readW fun p hp' => have := VG.Proof.Blake2.X86.Stream.saved_bound p hp'; VG.Proof.Blake2.X86.Stream.rw_scr hp.scr_fit _ _ (by omega) hd' (by omega)

theorem Saved.st {s₀ : State} (hp : VG.Proof.Blake2.X86.Stream.Update.Pre w s₀) {m m' : Mem} (h : VG.Proof.Blake2.X86.Stream.Saved (VG.Proof.Blake2.X86.Stream.Update.scr s₀) s₀ m)
    (hf : Frame [VG.Proof.Blake2.X86.Stream.Update.stR s₀ w] m m') : VG.Proof.Blake2.X86.Stream.Saved (VG.Proof.Blake2.X86.Stream.Update.scr s₀) s₀ m' :=
  Saved.keep hp.scr_fit h (hf.mono fun r hr => List.mem_cons_of_mem _ hr)
    (by simpa using hp.st_scr.symm)

theorem frame_scr {s₀ : State} (hp : VG.Proof.Blake2.X86.Stream.Update.Pre w s₀) {m : Mem} (hf : Frame [VG.Proof.Blake2.X86.Stream.Update.stR s₀ w, VG.Proof.Blake2.X86.Stream.Update.scR s₀, VG.Proof.Blake2.X86.Stream.Update.stkR s₀] s₀.mem m)
    {d : Nat} (hd : d + 4 ≤ 576) (v : BitVec 32) :
    Frame [VG.Proof.Blake2.X86.Stream.Update.stR s₀ w, VG.Proof.Blake2.X86.Stream.Update.scR s₀, VG.Proof.Blake2.X86.Stream.Update.stkR s₀] s₀.mem (m.writeW (addr (VG.Proof.Blake2.X86.Stream.Update.scr s₀) d) v) :=
  hf.writeW (by simp) _ (hp.scr_in hd)

theorem frame_st {s₀ : State} {m m' : Mem} (hf : Frame [VG.Proof.Blake2.X86.Stream.Update.stR s₀ w, VG.Proof.Blake2.X86.Stream.Update.scR s₀, VG.Proof.Blake2.X86.Stream.Update.stkR s₀] s₀.mem m)
    (hf' : Frame [VG.Proof.Blake2.X86.Stream.Update.stR s₀ w] m m') : Frame [VG.Proof.Blake2.X86.Stream.Update.stR s₀ w, VG.Proof.Blake2.X86.Stream.Update.scR s₀, VG.Proof.Blake2.X86.Stream.Update.stkR s₀] s₀.mem m' :=
  hf.trans (hf'.mono (by simp))

/-- The byte count is kept by writes to the buffer. -/
theorem Cnt.st {s₀ : State} (hp : VG.Proof.Blake2.X86.Stream.Update.Pre w s₀) {c : Nat} {m m' : Mem} (h : VG.Proof.Blake2.X86.Stream.Update.Cnt s₀ c m)
    (hf : Frame [VG.Proof.Blake2.X86.Stream.Update.stR s₀ w] m m') : VG.Proof.Blake2.X86.Stream.Update.Cnt s₀ c m' := by
  have k := fun d (h₁ : 512 ≤ d) (h₂ : d + 4 ≤ 576) =>
    VG.Proof.Blake2.X86.Stream.keep_hi hp.scr_fit (m := m) (m' := m') (rs := [VG.Proof.Blake2.X86.Stream.Update.stR s₀ w]) (hf.mono fun r hr => List.mem_cons_of_mem _ hr)
      (by simpa using hp.st_scr.symm) h₁ h₂
  exact ⟨(k cloOff (by decide) (by decide)).trans h.lo, (k chiOff (by decide) (by decide)).trans h.hi⟩

/-! ## `fill` -/

theorem fill_ok (hP : VG.Proof.Blake2.X86.Stream.Ok P) {s₀ : State} (hp : VG.Proof.Blake2.X86.Stream.Update.Pre w s₀) {c r : Nat} (hr : r ≤ blockBytes w) {s : State}
    (hI : VG.Proof.Blake2.X86.Stream.Update.Inv P s₀ c r s) (hptr : VG.Proof.Blake2.X86.Stream.Update.Ptr s₀ c s) (hcnt : VG.Proof.Blake2.X86.Stream.Update.Cnt s₀ c s.mem) (hax : s.gpr .eax = BitVec.ofNat 32 r) :
    WP isa (VG.Impl.Blake2.X86.Stream.fill w) s fun s' =>
      VG.Proof.Blake2.X86.Stream.Update.Inv P s₀ (c + min (blockBytes w - r) (VG.Proof.Blake2.X86.Stream.Update.len s₀ - c)) (r + min (blockBytes w - r) (VG.Proof.Blake2.X86.Stream.Update.len s₀ - c)) s' ∧
      VG.Proof.Blake2.X86.Stream.Update.Ptr s₀ (c + min (blockBytes w - r) (VG.Proof.Blake2.X86.Stream.Update.len s₀ - c)) s' ∧
      VG.Proof.Blake2.X86.Stream.Update.Cnt s₀ (c + min (blockBytes w - r) (VG.Proof.Blake2.X86.Stream.Update.len s₀ - c)) s'.mem := by
  have hl := hP.len
  have hL := VG.Proof.Blake2.X86.Stream.Update.len_lt s₀
  have hc := hI.c_le
  obtain ⟨a, ha⟩ : ∃ a, a = min (blockBytes w - r) (VG.Proof.Blake2.X86.Stream.Update.len s₀ - c) := ⟨_, rfl⟩
  rw [← ha]
  have ha₁ : a ≤ blockBytes w - r := ha ▸ Nat.min_le_left _ _
  have ha₂ : a ≤ VG.Proof.Blake2.X86.Stream.Update.len s₀ - c := ha ▸ Nat.min_le_right _ _
  unfold VG.Impl.Blake2.X86.Stream.fill
  refine WP.seq (wp_movi fun s₁ u₁ => wp_sub fun s₂ u₂ _ => wp_cmp fun s₃ f₃ cf₃ _ => WP.block_nil ?_)
  have hcx₂ : s₂.gpr .ecx = BitVec.ofNat 32 (blockBytes w - r) := by
    rw [u₂.gpr, u₁.gpr, u₁.other _ (by decide), hax, VG.Proof.Blake2.X86.Stream.B_eq, sub_ofNat hr]
  have hdi₂ : s₂.gpr .edi = BitVec.ofNat 32 (VG.Proof.Blake2.X86.Stream.Update.len s₀ - c) := by
    rw [u₂.other _ (by decide), u₁.other _ (by decide), hptr.edi]
  have g₃ : ∀ x, x ≠ .ecx → s₃.gpr x = s.gpr x := fun x h => by rw [f₃.gpr, u₂.other x h, u₁.other x h]
  -- `ecx` := `a`.
  refine WP.seq (WP.mono (Q := fun (t : State) => t.gpr .ecx = BitVec.ofNat 32 a ∧
      (∀ x, x ≠ .ecx → t.gpr x = s.gpr x) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr) ?_ fun t ht => ?_)
  · have hm : s₃.mem = s.mem := by rw [f₃.mem, u₂.mem, u₁.mem]
    have hrd : s₃.rd = s.rd := by rw [f₃.rd, u₂.rd, u₁.rd]
    have hwr : s₃.wr = s.wr := by rw [f₃.wr, u₂.wr, u₁.wr]
    have hcf : isa.eval .b s₃ = some (decide (VG.Proof.Blake2.X86.Stream.Update.len s₀ - c < blockBytes w - r)) := by
      show s₃.cf = _
      rw [cf₃, hdi₂, hcx₂, toNat_ofNat_lt (by omega), toNat_ofNat_lt (by omega)]
    refine WP.ite _ hcf (fun hb => ?_) (fun hb => ?_)
    · simp only [decide_eq_true_eq] at hb
      refine wp_mov fun s₄ u₄ => WP.block_nil ⟨?_, fun x h => by rw [u₄.other x h, g₃ x h],
        by rw [u₄.mem, hm], by rw [u₄.rd, hrd], by rw [u₄.wr, hwr]⟩
      rw [u₄.gpr, f₃.gpr, hdi₂, ha, Nat.min_eq_right (by omega)]
    · simp only [decide_eq_false_iff_not] at hb
      refine WP.block_nil ⟨?_, g₃, hm, hrd, hwr⟩
      rw [f₃.gpr, hcx₂, ha, Nat.min_eq_left (by omega)]
  obtain ⟨tcx, tg, tm, trd, twr⟩ := ht
  have tbp : t.gpr .ebp = VG.Proof.Blake2.X86.Stream.Update.scr s₀ := by rw [tg _ (by decide), hI.ebp]
  have trd' : t.rd = s₀.rd := trd.trans hI.rd
  have twr' : t.wr = s₀.wr := twr.trans hI.wr
  refine WP.seq (wp_sub fun s₅ u₅ _ => wp_mov fun s₆ u₆ => wp_add fun s₇ u₇ _ => ?_)
  have g₇ : ∀ x, x ≠ .edx → x ≠ .edi → s₇.gpr x = t.gpr x := fun x h1 h2 => by
    rw [u₇.other x h1, u₆.other x h1, u₅.other x h2]
  have m₇ : s₇.mem = s.mem := by rw [u₇.mem, u₆.mem, u₅.mem, tm]
  have rd₇ : s₇.rd = s₀.rd := by rw [u₇.rd, u₆.rd, u₅.rd, trd']
  have wr₇ : s₇.wr = s₀.wr := by rw [u₇.wr, u₆.wr, u₅.wr, twr']
  have bp₇ : s₇.gpr .ebp = VG.Proof.Blake2.X86.Stream.Update.scr s₀ := by rw [g₇ _ (by decide) (by decide), tbp]
  have cx₇ : s₇.gpr .ecx = BitVec.ofNat 32 a := by rw [g₇ _ (by decide) (by decide), tcx]
  -- The byte count.
  refine VG.Proof.Blake2.X86.Stream.wp_ldmF bp₇ (hp.sinr rd₇ wr₇ (d := cloOff) (by decide)) fun s₈ u₈ _ _ => ?_
  refine wp_add fun s₉ u₉ cf₉ => ?_
  refine wp_stm (o := cloOff) (by rw [u₉.other _ (by decide), u₈.other _ (by decide), bp₇])
    (by rw [u₉.wr, u₈.wr, wr₇]; exact hp.sin rfl (by decide)) fun s₁₀ u₁₀ => ?_
  have bp₁₀ : s₁₀.gpr .ebp = VG.Proof.Blake2.X86.Stream.Update.scr s₀ := by rw [u₁₀.gpr, u₉.other _ (by decide), u₈.other _ (by decide), bp₇]
  have ichi := hp.sinr rd₇ wr₇ (d := chiOff) (by decide)
  refine VG.Proof.Blake2.X86.Stream.wp_ldmF bp₁₀ (by rw [u₁₀.rd, u₁₀.wr, u₉.rd, u₉.wr, u₈.rd, u₈.wr]; exact ichi)
    fun s₁₁ u₁₁ cf₁₁ _ => ?_
  refine VG.Proof.Blake2.X86.Stream.wp_adc0 (by rw [cf₁₁, u₁₀.cf, cf₉]) fun s₁₂ u₁₂ => ?_
  refine wp_stm (o := chiOff) (by rw [u₁₂.other _ (by decide), u₁₁.other _ (by decide), bp₁₀])
    (by rw [u₁₂.wr, u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, wr₇]; exact hp.sin rfl (by decide)) fun s₁₃ u₁₃ => ?_
  refine wp_test fun s₁₄ f₁₄ z₁₄ => WP.block_nil ?_
  -- The state after the block.
  have g₁₄ : ∀ x, x ≠ .eax → s₁₄.gpr x = s₇.gpr x := fun x h => by
    rw [f₁₄.gpr, u₁₃.gpr, u₁₂.other x h, u₁₁.other x h, u₁₀.gpr, u₉.other x h, u₈.other x h]
  have rd₁₄ : s₁₄.rd = s₀.rd := by rw [f₁₄.rd, u₁₃.rd, u₁₂.rd, u₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd, rd₇]
  have wr₁₄ : s₁₄.wr = s₀.wr := by rw [f₁₄.wr, u₁₃.wr, u₁₂.wr, u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, wr₇]
  have lo₉ : s₉.gpr .eax = BitVec.ofNat 32 (VG.Proof.Blake2.X86.Stream.Update.cnt s₀ + (c + a)) := by
    rw [u₉.gpr, u₈.gpr, u₈.other _ (by decide), cx₇, m₇, hcnt.lo, ← BitVec.ofNat_add, Nat.add_assoc]
  have m₁₀ : s₁₀.mem = s.mem.writeW (addr (VG.Proof.Blake2.X86.Stream.Update.scr s₀) cloOff) (BitVec.ofNat 32 (VG.Proof.Blake2.X86.Stream.Update.cnt s₀ + (c + a))) := by
    rw [u₁₀.mem, lo₉, u₉.mem, u₈.mem, m₇]
  have hi₁₂ : s₁₂.gpr .eax = BitVec.ofNat 32 ((VG.Proof.Blake2.X86.Stream.Update.cnt s₀ + (c + a)) / 2 ^ 32) := by
    rw [u₁₂.gpr, u₁₁.gpr, m₁₀, VG.Proof.Blake2.X86.Stream.rw_scr hp.scr_fit _ _ (by decide) (by decide) (by decide), hcnt.hi,
      u₈.gpr, u₈.other _ (by decide), cx₇, m₇, hcnt.lo, VG.Proof.Blake2.X86.Stream.carry_ofNat _ _ (by omega), Nat.add_assoc]
  have m₁₄ : s₁₄.mem = (s.mem.writeW (addr (VG.Proof.Blake2.X86.Stream.Update.scr s₀) cloOff) (BitVec.ofNat 32 (VG.Proof.Blake2.X86.Stream.Update.cnt s₀ + (c + a)))).writeW
      (addr (VG.Proof.Blake2.X86.Stream.Update.scr s₀) chiOff) (BitVec.ofNat 32 ((VG.Proof.Blake2.X86.Stream.Update.cnt s₀ + (c + a)) / 2 ^ 32)) := by
    rw [f₁₄.mem, u₁₃.mem, hi₁₂, u₁₂.mem, u₁₁.mem, m₁₀]
  have hcnt₁₄ : VG.Proof.Blake2.X86.Stream.Update.Cnt s₀ (c + a) s₁₄.mem :=
    ⟨by rw [m₁₄, VG.Proof.Blake2.X86.Stream.rw_scr hp.scr_fit _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32],
      by rw [m₁₄, Mem.readW_writeW_self32]⟩
  have hfr₁₄ : Frame [VG.Proof.Blake2.X86.Stream.Update.stR s₀ w, VG.Proof.Blake2.X86.Stream.Update.scR s₀, VG.Proof.Blake2.X86.Stream.Update.stkR s₀] s₀.mem s₁₄.mem := by
    rw [m₁₄]; exact VG.Proof.Blake2.X86.Stream.Update.frame_scr hp (VG.Proof.Blake2.X86.Stream.Update.frame_scr hp hI.frame (by decide) _) (by decide) _
  have hsv₁₄ : VG.Proof.Blake2.X86.Stream.Saved (VG.Proof.Blake2.X86.Stream.Update.scr s₀) s₀ s₁₄.mem := by
    rw [m₁₄]; exact Saved.write hp (Saved.write hp hI.saved (by decide) (by decide) _) (by decide) (by decide) _
  have hst₁₄ : ∀ i < bufOff w + blockBytes w,
      s₁₄.mem (VG.Proof.Blake2.X86.Stream.Update.stA s₀ + BitVec.ofNat 64 i) = s.mem (VG.Proof.Blake2.X86.Stream.Update.stA s₀ + BitVec.ofNat 64 i) := by
    refine VG.Proof.Blake2.X86.Stream.Update.st_keep hP hp ?_
    rw [m₁₄]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (hp.scr_in (by decide))).writeW
      (List.mem_singleton_self _) _ (hp.scr_in (by decide))
  have di₁₄ : s₁₄.gpr .edi = BitVec.ofNat 32 (VG.Proof.Blake2.X86.Stream.Update.len s₀ - (c + a)) := by
    rw [g₁₄ _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, tg _ (by decide), tcx,
      hptr.edi, sub_ofNat (by omega), Nat.sub_sub]
  have dx₁₄ : s₁₄.gpr .edx = VG.Proof.Blake2.X86.Stream.Update.st s₀ + BitVec.ofNat 32 r := by
    rw [g₁₄ _ (by decide), u₇.gpr, u₆.gpr, u₆.other _ (by decide), u₅.other .ebx (by decide),
      u₅.other .eax (by decide), tg .ebx (by decide), tg .eax (by decide), hI.ebx, hax]
  have hz : isa.eval .e s₁₄ = some (decide (a = 0)) := by
    show s₁₄.zf = _
    rw [z₁₄, u₁₃.gpr, u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.gpr, u₉.other _ (by decide),
      u₈.other _ (by decide), cx₇, BitVec.and_self, ofNat_beq_zero (by omega)]
  have hC₁₄ : VG.Proof.Blake2.X86.Stream.Update.Common w s₀ c s₁₄ :=
    ⟨hc, rd₁₄, wr₁₄, by rw [g₁₄ _ (by decide), g₇ _ (by decide) (by decide), tg _ (by decide), hI.ebx],
      by rw [g₁₄ _ (by decide), bp₇], by rw [g₁₄ _ (by decide), g₇ _ (by decide) (by decide),
        tg _ (by decide), hI.esp], hfr₁₄, hsv₁₄⟩
  have si₁₄ : s₁₄.gpr .esi = VG.Proof.Blake2.X86.Stream.Update.dp s₀ + BitVec.ofNat 32 c := by
    rw [g₁₄ _ (by decide), g₇ _ (by decide) (by decide), tg _ (by decide), hptr.esi]
  refine WP.ite _ hz (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    subst hb
    refine WP.block_nil ⟨{ hC₁₄ with c_le := by omega, repr := fun h0 d hd => ?_ }, ⟨si₁₄, di₁₄⟩, hcnt₁₄⟩
    exact VG.Proof.Blake2.X86.Stream.reprR_congr hP hst₁₄ (hI.repr h0 d hd)
  · simp only [decide_eq_false_iff_not] at hb
    refine WP.mono (VG.Proof.Blake2.X86.Stream.Update.copy_ok hP hp (c := c) (r := r) (k := a) (by omega) (by omega) (by omega) rd₁₄ wr₁₄
      si₁₄ dx₁₄ (by rw [f₁₄.gpr, u₁₃.gpr, u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.gpr,
        u₉.other _ (by decide), u₈.other _ (by decide), cx₇]) hfr₁₄
      (fun h0 d hd => VG.Proof.Blake2.X86.Stream.reprR_congr hP hst₁₄ (hI.repr h0 d hd)))
      fun s₁₅ ⟨g₁₅, si₁₅, rd₁₅, wr₁₅, f₁₅, rp₁₅⟩ => ?_
    refine ⟨⟨⟨by omega, rd₁₅, wr₁₅, ?_, ?_, ?_, VG.Proof.Blake2.X86.Stream.Update.frame_st hfr₁₄ f₁₅, Saved.st hp hsv₁₄ f₁₅⟩, rp₁₅⟩,
      ⟨si₁₅, ?_⟩, Cnt.st hp hcnt₁₄ f₁₅⟩
    · rw [g₁₅ _ (by decide) (by decide) (by decide) (by decide)]; exact hC₁₄.ebx
    · rw [g₁₅ _ (by decide) (by decide) (by decide) (by decide)]; exact hC₁₄.ebp
    · rw [g₁₅ _ (by decide) (by decide) (by decide) (by decide)]; exact hC₁₄.esp
    · rw [g₁₅ _ (by decide) (by decide) (by decide) (by decide)]; exact di₁₄

/-! ## Calling the compression function -/

/-- A call of the compression function on the (full) buffer or on blocks of
data, without the final block flag. -/
theorem call_upd (hP : VG.Proof.Blake2.X86.Stream.Ok P) {name : String} {code : Prog isa} (hf : VG.Proof.Blake2.X86.Stream.CalleeOk P code) {s₀ : State}
    (hp : VG.Proof.Blake2.X86.Stream.Update.Pre w s₀) {s : State} {blk tlo thi : BitVec 32} {k : Nat}
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (hesp : s.gpr .esp = VG.Proof.Blake2.X86.Stream.Update.esp₀ s₀) (hS : s.gpr .ebx = VG.Proof.Blake2.X86.Stream.Update.st s₀)
    (hC : s.gpr .ebp = VG.Proof.Blake2.X86.Stream.Update.scr s₀) (hB : s.gpr .esi = blk) (hk : (s.gpr .edi).toNat = k)
    (hlo : s.gpr .ecx = tlo) (hhi : s.gpr .edx = thi) (hl : s.gpr .eax = 0)
    (hsrc : (blk = VG.Proof.Blake2.X86.Stream.Update.st s₀ + BitVec.ofNat 32 (bufOff w) ∧ k = 1) ∨
      ∃ c₀, blk = VG.Proof.Blake2.X86.Stream.Update.dp s₀ + BitVec.ofNat 32 c₀ ∧ c₀ + blockBytes w * k ≤ VG.Proof.Blake2.X86.Stream.Update.len s₀ ∧ 0 < k)
    {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame [⟨VG.Proof.Blake2.X86.Stream.Update.stA s₀, bufOff w⟩, ⟨VG.Proof.Blake2.X86.Stream.Update.scA s₀, 512⟩, VG.Proof.Blake2.X86.Stream.Update.stkR s₀] s.mem s'.mem →
      VG.Spec.Blake2.stateAt w s'.mem (VG.Proof.Blake2.X86.Stream.Update.stA s₀) =
        VG.Spec.Blake2.compressBlocks P (VG.Spec.Blake2.stateAt w s.mem (VG.Proof.Blake2.X86.Stream.Update.stA s₀)) s.mem (blk.setWidth 64) k (thi ++ tlo).toNat false →
      Q s') :
    WP isa (compressCall name code) s Q := by
  have hl' := hP.len
  have fS := hp.st_fit; have fD := hp.d_fit; have fC := hp.scr_fit
  have hN := hP.N
  have eN : Region.Sub ⟨VG.Proof.Blake2.X86.Stream.Update.stA s₀, bufOff w⟩ (VG.Proof.Blake2.X86.Stream.Update.stR s₀ w) := Region.sub_prefix (by omega)
  have eso : Region.Sub ⟨VG.Proof.Blake2.X86.Stream.Update.scA s₀, 512⟩ (VG.Proof.Blake2.X86.Stream.Update.scR s₀) := Region.sub_prefix (by omega)
  -- Where the blocks are.
  have hblk : blk.toNat + blockBytes w * k ≤ 2 ^ 32 ∧
      (Region.Sub ⟨blk.setWidth 64, blockBytes w * k⟩ (VG.Proof.Blake2.X86.Stream.Update.stR s₀ w) ∧
        Region.Disjoint ⟨blk.setWidth 64, blockBytes w * k⟩ ⟨VG.Proof.Blake2.X86.Stream.Update.stA s₀, bufOff w⟩ ∨
       Region.Sub ⟨blk.setWidth 64, blockBytes w * k⟩ (VG.Proof.Blake2.X86.Stream.Update.dR s₀)) ∧
      ∃ r ∈ s₀.rd ++ s₀.wr, ∃ o, (blk.setWidth 64) = r.base + BitVec.ofNat 64 o ∧
        o + blockBytes w * k ≤ r.len := by
    rcases hsrc with ⟨rfl, rfl⟩ | ⟨c₀, rfl, hc₀, hk0⟩
    · have e := VG.Proof.Blake2.X86.Stream.sw_add (x := VG.Proof.Blake2.X86.Stream.Update.st s₀) (c := bufOff w) (by omega)
      refine ⟨by rw [VG.Proof.Blake2.X86.Stream.toNat_add_ofNat (by omega)]; omega, .inl ⟨by rw [e]; exact sub_offset (by omega) (by omega),
        by rw [e]; exact Offset.disjoint_base _ (Nat.le_refl _) (by omega)⟩, VG.Proof.Blake2.X86.Stream.Update.stR s₀ w, by simp [hp.wr],
        bufOff w, e, by simp only; omega⟩
    · have hB1 : blockBytes w ≤ blockBytes w * k := Nat.le_mul_of_pos_right _ hk0
      have e := VG.Proof.Blake2.X86.Stream.sw_add (x := VG.Proof.Blake2.X86.Stream.Update.dp s₀) (c := c₀) (by have := hP.pos; omega)
      refine ⟨by rw [VG.Proof.Blake2.X86.Stream.toNat_add_ofNat (by have := hP.pos; omega)]; omega,
        .inr (by rw [e]; exact sub_offset (by omega) (by omega)), VG.Proof.Blake2.X86.Stream.Update.dR s₀, by simp [hp.rd], c₀, e, hc₀⟩
  obtain ⟨f₁, hsub, r₀, hr₀, o₀, ho₀, hl₀⟩ := hblk
  have dS : (VG.Proof.Blake2.X86.Stream.Update.stkR s₀).Disjoint ⟨VG.Proof.Blake2.X86.Stream.Update.stA s₀, bufOff w⟩ := hp.stk_st.sub_right eN
  have dC : (VG.Proof.Blake2.X86.Stream.Update.stkR s₀).Disjoint ⟨VG.Proof.Blake2.X86.Stream.Update.scA s₀, 512⟩ := hp.stk_scr.sub_right eso
  refine VG.Proof.Blake2.X86.Stream.call_ok (P := P) hf hesp hS hC hB hk hlo hhi hl hp.sp_lo (by omega) f₁ (by omega)
    ((hp.st_scr.sub_left eN).sub_right eso) ?_ ?_ dS dC ?_ ?_ ?_
    fun s' rd' wr' cs' f' post => hQ s' rd' wr' cs' f' (by rw [post]; rfl)
  · rcases hsub with ⟨_, h⟩ | h
    · exact h
    · exact (hp.d_st.sub_left h).sub_right eN
  · rcases hsub with ⟨h, _⟩ | h
    · exact (hp.st_scr.sub_left h).sub_right eso
    · exact (hp.d_scr.sub_left h).sub_right eso
  · rcases hsub with ⟨h, _⟩ | h
    · exact hp.stk_st.sub_right h
    · exact hp.stk_d.sub_right h
  · rw [hrd, hwr]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨r₀, hr₀, o₀, ho₀, hl₀⟩
  · rw [hwr, hp.wr]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨VG.Proof.Blake2.X86.Stream.Update.stR s₀ w, by simp, 0, by simp, by simp⟩
    · exact ⟨VG.Proof.Blake2.X86.Stream.Update.scR s₀, by simp, 0, by simp, by simp⟩

/-- A call keeps what holds throughout. -/
theorem Common.after_call (hP : VG.Proof.Blake2.X86.Stream.Ok P) {s₀ : State} (hp : VG.Proof.Blake2.X86.Stream.Update.Pre w s₀) {c : Nat} {s s' : State}
    (h : VG.Proof.Blake2.X86.Stream.Update.Common w s₀ c s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hcs : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r)
    (hf : Frame [⟨VG.Proof.Blake2.X86.Stream.Update.stA s₀, bufOff w⟩, ⟨VG.Proof.Blake2.X86.Stream.Update.scA s₀, 512⟩, VG.Proof.Blake2.X86.Stream.Update.stkR s₀] s.mem s'.mem) :
    VG.Proof.Blake2.X86.Stream.Update.Common w s₀ c s' := by
  have hl := hP.len
  have hf' : Frame (⟨VG.Proof.Blake2.X86.Stream.Update.scA s₀, 512⟩ :: [VG.Proof.Blake2.X86.Stream.Update.stR s₀ w, VG.Proof.Blake2.X86.Stream.Update.stkR s₀]) s.mem s'.mem := hf.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨VG.Proof.Blake2.X86.Stream.Update.stR s₀ w, by simp, Region.sub_prefix (by omega)⟩
    · exact ⟨⟨VG.Proof.Blake2.X86.Stream.Update.scA s₀, 512⟩, by simp, fun _ h => h⟩
    · exact ⟨VG.Proof.Blake2.X86.Stream.Update.stkR s₀, by simp, fun _ h => h⟩
  exact ⟨h.c_le, hrd.trans h.rd, hwr.trans h.wr, by rw [hcs _ (by decide)]; exact h.ebx,
    by rw [hcs _ (by decide)]; exact h.ebp, by rw [hcs _ (by decide)]; exact h.esp,
    h.frame.trans (hf'.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨VG.Proof.Blake2.X86.Stream.Update.scR s₀, by simp, Region.sub_prefix (by omega)⟩
      · exact ⟨VG.Proof.Blake2.X86.Stream.Update.stR s₀ w, by simp, fun _ h => h⟩
      · exact ⟨VG.Proof.Blake2.X86.Stream.Update.stkR s₀, by simp, fun _ h => h⟩),
    Saved.keep hp.scr_fit h.saved hf' hp.scr_disj⟩

/-- A word of the scratch space from offset 512 on is kept by a call. -/
theorem keep_call {s₀ : State} (hp : VG.Proof.Blake2.X86.Stream.Update.Pre w s₀) {m m' : Mem}
    (hf : Frame [⟨VG.Proof.Blake2.X86.Stream.Update.stA s₀, bufOff w⟩, ⟨VG.Proof.Blake2.X86.Stream.Update.scA s₀, 512⟩, VG.Proof.Blake2.X86.Stream.Update.stkR s₀] m m') {d : Nat} (h₁ : 512 ≤ d) (h₂ : d + 4 ≤ 576) :
    m'.readW (addr (VG.Proof.Blake2.X86.Stream.Update.scr s₀) d) 32 = m.readW (addr (VG.Proof.Blake2.X86.Stream.Update.scr s₀) d) 32 := by
  refine VG.Proof.Blake2.X86.Stream.keep_hi hp.scr_fit (rs := [VG.Proof.Blake2.X86.Stream.Update.stR s₀ w, VG.Proof.Blake2.X86.Stream.Update.stkR s₀]) (hf.sub fun r hr => ?_) hp.scr_disj h₁ h₂
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨VG.Proof.Blake2.X86.Stream.Update.stR s₀ w, by simp, Region.sub_prefix (by have := hp.st_fit; omega)⟩
  · exact ⟨⟨VG.Proof.Blake2.X86.Stream.Update.scA s₀, 512⟩, by simp, fun _ h => h⟩
  · exact ⟨VG.Proof.Blake2.X86.Stream.Update.stkR s₀, by simp, fun _ h => h⟩

theorem compressBlocks_one (h : VG.Spec.Blake2.HashValue w) (m : Mem) (p : Addr) (t : Nat) (f : Bool) :
    VG.Spec.Blake2.compressBlocks P h m p 1 t f = F P h (VG.Spec.Blake2.blockAt w m p) t f := by
  rw [compressBlocks_succ, compressBlocks_zero]; simp

/-! ## Compressing the full buffer -/

theorem compressBuf_ok (hP : VG.Proof.Blake2.X86.Stream.Ok P) {name : String} {code : Prog isa} (hf : VG.Proof.Blake2.X86.Stream.CalleeOk P code) {s₀ : State}
    (hp : VG.Proof.Blake2.X86.Stream.Update.Pre w s₀) {c : Nat} {s : State} (hI : VG.Proof.Blake2.X86.Stream.Update.Inv P s₀ c (blockBytes w) s) (hptr : VG.Proof.Blake2.X86.Stream.Update.Ptr s₀ c s)
    (hcnt : VG.Proof.Blake2.X86.Stream.Update.Cnt s₀ c s.mem) :
    WP isa (compressBuf w name code) s fun s' => VG.Proof.Blake2.X86.Stream.Update.Inv P s₀ c 0 s' ∧ VG.Proof.Blake2.X86.Stream.Update.Ptr s₀ c s' ∧ VG.Proof.Blake2.X86.Stream.Update.Cnt s₀ c s'.mem := by
  have hl := hP.len
  unfold compressBuf
  have bp := hI.ebp
  refine WP.seq (wp_stm (o := dataOff) bp (hp.sin hI.wr (by decide)) fun s₁ u₁ => ?_)
  refine wp_stm (o := lenOff) (by rw [u₁.gpr, bp]) (by rw [u₁.wr]; exact hp.sin hI.wr (by decide))
    fun s₂ u₂ => ?_
  refine wp_mov fun s₃ u₃ => wp_addi fun s₄ u₄ => wp_movi fun s₅ u₅ => ?_
  have g₅ : ∀ x, x ≠ .esi → x ≠ .edi → s₅.gpr x = s.gpr x := fun x h1 h2 => by
    rw [u₅.other x h2, u₄.other x h1, u₃.other x h1, u₂.gpr, u₁.gpr]
  have rd₅ : s₅.rd = s₀.rd := by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, hI.rd]
  have wr₅ : s₅.wr = s₀.wr := by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, hI.wr]
  have m₂ : s₂.mem = (s.mem.writeW (addr (VG.Proof.Blake2.X86.Stream.Update.scr s₀) dataOff) (s.gpr .esi)).writeW (addr (VG.Proof.Blake2.X86.Stream.Update.scr s₀) lenOff)
      (s.gpr .edi) := by rw [u₂.mem, u₁.mem, u₁.gpr]
  have m₅ : s₅.mem = s₂.mem := by rw [u₅.mem, u₄.mem, u₃.mem]
  have bp₅ : s₅.gpr .ebp = VG.Proof.Blake2.X86.Stream.Update.scr s₀ := by rw [g₅ _ (by decide) (by decide), bp]
  refine wp_ldm bp₅ (hp.sinr rd₅ wr₅ (d := cloOff) (by decide)) fun s₆ u₆ => ?_
  have ichi := hp.sinr rd₅ wr₅ (d := chiOff) (by decide)
  refine wp_ldm (by rw [u₆.other _ (by decide), bp₅]) (by rw [u₆.rd, u₆.wr]; exact ichi) fun s₇ u₇ => ?_
  refine wp_movi fun s₈ u₈ => WP.block_nil ?_
  have g₈ : ∀ x, x ≠ .esi → x ≠ .edi → x ≠ .ecx → x ≠ .edx → x ≠ .eax → s₈.gpr x = s.gpr x :=
    fun x h1 h2 h3 h4 h5 => by rw [u₈.other x h5, u₇.other x h4, u₆.other x h3, g₅ x h1 h2]
  have m₈ : s₈.mem = s₂.mem := by rw [u₈.mem, u₇.mem, u₆.mem, m₅]
  -- The memory before the call: only the two words of the scratch space differ.
  have fr₂ : Frame [VG.Proof.Blake2.X86.Stream.Update.scR s₀] s.mem s₂.mem := by
    rw [m₂]; exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (hp.scr_in (by decide))).writeW
      (List.mem_singleton_self _) _ (hp.scr_in (by decide))
  have rd₂ : s₂.mem.readW (addr (VG.Proof.Blake2.X86.Stream.Update.scr s₀) cloOff) 32 = s.mem.readW (addr (VG.Proof.Blake2.X86.Stream.Update.scr s₀) cloOff) 32 := by
    rw [m₂, VG.Proof.Blake2.X86.Stream.rw_scr hp.scr_fit _ _ (by decide) (by decide) (by decide),
      VG.Proof.Blake2.X86.Stream.rw_scr hp.scr_fit _ _ (by decide) (by decide) (by decide)]
  have rd₂' : s₂.mem.readW (addr (VG.Proof.Blake2.X86.Stream.Update.scr s₀) chiOff) 32 = s.mem.readW (addr (VG.Proof.Blake2.X86.Stream.Update.scr s₀) chiOff) 32 := by
    rw [m₂, VG.Proof.Blake2.X86.Stream.rw_scr hp.scr_fit _ _ (by decide) (by decide) (by decide),
      VG.Proof.Blake2.X86.Stream.rw_scr hp.scr_fit _ _ (by decide) (by decide) (by decide)]
  refine WP.seq (VG.Proof.Blake2.X86.Stream.Update.call_upd hP hf hp (blk := VG.Proof.Blake2.X86.Stream.Update.st s₀ + BitVec.ofNat 32 (bufOff w)) (k := 1)
    (tlo := BitVec.ofNat 32 (VG.Proof.Blake2.X86.Stream.Update.cnt s₀ + c)) (thi := BitVec.ofNat 32 ((VG.Proof.Blake2.X86.Stream.Update.cnt s₀ + c) / 2 ^ 32))
    (by rw [u₈.rd, u₇.rd, u₆.rd, rd₅]) (by rw [u₈.wr, u₇.wr, u₆.wr, wr₅])
    (by rw [g₈ _ (by decide) (by decide) (by decide) (by decide) (by decide), hI.esp])
    (by rw [g₈ _ (by decide) (by decide) (by decide) (by decide) (by decide), hI.ebx])
    (by rw [g₈ _ (by decide) (by decide) (by decide) (by decide) (by decide), bp])
    (by rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.gpr, u₃.gpr, u₂.gpr, u₁.gpr, hI.ebx, VG.Proof.Blake2.X86.Stream.N_eq])
    (by rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr]; rfl)
    (by rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, m₅, rd₂, hcnt.lo])
    (by rw [u₈.other _ (by decide), u₇.gpr, u₆.mem, m₅, rd₂', hcnt.hi]) u₈.gpr (.inl ⟨rfl, rfl⟩)
    fun s' rd' wr' cs' f' post => ?_)
  have sv₂ := Saved.write hp (Saved.write hp hI.saved (d := dataOff) (by decide) (by decide) (s.gpr .esi))
    (d := lenOff) (by decide) (by decide) (s.gpr .edi)
  have hC₈ : VG.Proof.Blake2.X86.Stream.Update.Common w s₀ c s₈ :=
    ⟨hI.c_le, by rw [u₈.rd, u₇.rd, u₆.rd, rd₅], by rw [u₈.wr, u₇.wr, u₆.wr, wr₅],
      by rw [g₈ _ (by decide) (by decide) (by decide) (by decide) (by decide), hI.ebx],
      by rw [g₈ _ (by decide) (by decide) (by decide) (by decide) (by decide), bp],
      by rw [g₈ _ (by decide) (by decide) (by decide) (by decide) (by decide), hI.esp],
      by rw [m₈, m₂]; exact VG.Proof.Blake2.X86.Stream.Update.frame_scr hp (VG.Proof.Blake2.X86.Stream.Update.frame_scr hp hI.frame (by decide) _) (by decide) _,
      by rw [m₈, m₂]; exact sv₂⟩
  have hC' : VG.Proof.Blake2.X86.Stream.Update.Common w s₀ c s' := hC₈.after_call hP hp rd' wr' cs' f'
  have kc : ∀ d, 512 ≤ d → d + 4 ≤ 576 → s'.mem.readW (addr (VG.Proof.Blake2.X86.Stream.Update.scr s₀) d) 32 = s₈.mem.readW (addr (VG.Proof.Blake2.X86.Stream.Update.scr s₀) d) 32 :=
    fun _ h₁ h₂ => VG.Proof.Blake2.X86.Stream.Update.keep_call hp f' h₁ h₂
  refine wp_ldm (b := .ebp) hC'.ebp (hp.sinr hC'.rd hC'.wr (d := dataOff) (by decide)) fun s₉ u₉ => ?_
  have ilen := hp.sinr hC'.rd hC'.wr (d := lenOff) (by decide)
  refine wp_ldm (b := .ebp) (by rw [u₉.other _ (by decide), hC'.ebp]) (by rw [u₉.rd, u₉.wr]; exact ilen)
    fun s₁₀ u₁₀ => WP.block_nil ?_
  have g₁₀ : ∀ x, x ≠ .esi → x ≠ .edi → s₁₀.gpr x = s'.gpr x := fun x h1 h2 => by
    rw [u₁₀.other x h2, u₉.other x h1]
  have m₁₀ : s₁₀.mem = s'.mem := by rw [u₁₀.mem, u₉.mem]
  have hC₁₀ : VG.Proof.Blake2.X86.Stream.Update.Common w s₀ c s₁₀ := hC'.of_gpr (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact g₁₀ _ (by decide) (by decide)) m₁₀
    (by rw [u₁₀.rd, u₉.rd]) (by rw [u₁₀.wr, u₉.wr])
  refine ⟨{ hC₁₀ with repr := fun h0 d hd => ?_ }, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · have hcn := hd.cnt_eq
    have hlt := hd.2.2
    have hc := hI.c_le
    rw [m₁₀]
    refine reprR_flush P hP.pos (mem := s₂.mem) (VG.Proof.Blake2.X86.Stream.reprR_congr hP (VG.Proof.Blake2.X86.Stream.Update.st_keep hP hp fr₂) (hI.repr h0 d hd)) ?_
    rw [post, m₈, VG.Proof.Blake2.X86.Stream.Update.compressBlocks_one, VG.Proof.Blake2.X86.Stream.sw_add (by have := hp.st_fit; have := hP.pos; omega), VG.Proof.Blake2.X86.Stream.append_ofNat (by omega),
      List.length_append, VG.Proof.Blake2.X86.Stream.Update.D_length, ← hcn]
  · rw [u₁₀.other _ (by decide), u₉.gpr, kc dataOff (by decide) (by decide), m₈, m₂,
      VG.Proof.Blake2.X86.Stream.rw_scr hp.scr_fit _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32, hptr.esi]
  · rw [u₁₀.gpr, u₉.mem, kc lenOff (by decide) (by decide), m₈, m₂, Mem.readW_writeW_self32, hptr.edi]
  · rw [m₁₀, kc cloOff (by decide) (by decide), m₈, rd₂, hcnt.lo]
  · rw [m₁₀, kc chiOff (by decide) (by decide), m₈, rd₂', hcnt.hi]

/-! ## `head`: filling the buffer -/

/-- After `head`: all the data is in, with the buffer not empty, or the
buffer is empty and data is left. -/
def HeadPost (P : VG.Spec.Blake2.Params w) (s₀ : State) (s : State) : Prop :=
  ∃ c r, VG.Proof.Blake2.X86.Stream.Update.Inv P s₀ c r s ∧ VG.Proof.Blake2.X86.Stream.Update.Ptr s₀ c s ∧ VG.Proof.Blake2.X86.Stream.Update.Cnt s₀ c s.mem ∧ ((c = VG.Proof.Blake2.X86.Stream.Update.len s₀ ∧ 1 ≤ r) ∨ (c < VG.Proof.Blake2.X86.Stream.Update.len s₀ ∧ r = 0))

theorem head_ok (hP : VG.Proof.Blake2.X86.Stream.Ok P) {name : String} {code : Prog isa} (hf : VG.Proof.Blake2.X86.Stream.CalleeOk P code) {s₀ : State}
    (hp : VG.Proof.Blake2.X86.Stream.Update.Pre w s₀) {r : Nat} (hr : r ≤ blockBytes w) (hl : 0 < VG.Proof.Blake2.X86.Stream.Update.len s₀) {s : State} (hI : VG.Proof.Blake2.X86.Stream.Update.Inv P s₀ 0 r s)
    (hptr : VG.Proof.Blake2.X86.Stream.Update.Ptr s₀ 0 s) (hcnt : VG.Proof.Blake2.X86.Stream.Update.Cnt s₀ 0 s.mem) (hax : s.gpr .eax = BitVec.ofNat 32 r) :
    WP isa (head w name code) s (VG.Proof.Blake2.X86.Stream.Update.HeadPost P s₀) := by
  have hL := VG.Proof.Blake2.X86.Stream.Update.len_lt s₀
  have hl' := hP.len
  unfold head
  refine WP.seq (wp_test fun s₁ f₁ z₁ => WP.block_nil ?_)
  have hI₁ := hI.of_gpr (fun r _ => by rw [f₁.gpr]) f₁.mem f₁.rd f₁.wr
  have hptr₁ := hptr.of_gpr (by rw [f₁.gpr]) (by rw [f₁.gpr])
  have hz : isa.eval .e s₁ = some (decide (r = 0)) := by
    show s₁.zf = _
    rw [z₁, hax, BitVec.and_self, ofNat_beq_zero (by omega)]
  refine WP.ite _ hz (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    subst hb
    exact WP.block_nil ⟨0, 0, hI₁, hptr₁, by rw [f₁.mem]; exact hcnt, .inr ⟨hl, rfl⟩⟩
  · simp only [decide_eq_false_iff_not] at hb
    refine WP.seq (WP.mono (VG.Proof.Blake2.X86.Stream.Update.fill_ok hP hp hr hI₁ hptr₁ (by rw [f₁.mem]; exact hcnt) (by rw [f₁.gpr]; exact hax))
      fun s₂ ⟨hI₂, hptr₂, hcnt₂⟩ => ?_)
    rw [Nat.zero_add, Nat.sub_zero] at hI₂ hptr₂ hcnt₂
    refine WP.seq (wp_test fun s₃ f₃ z₃ => WP.block_nil ?_)
    have hI₃ := hI₂.of_gpr (fun r _ => by rw [f₃.gpr]) f₃.mem f₃.rd f₃.wr
    have hptr₃ := hptr₂.of_gpr (by rw [f₃.gpr]) (by rw [f₃.gpr])
    have hcnt₃ : VG.Proof.Blake2.X86.Stream.Update.Cnt s₀ (min (blockBytes w - r) (VG.Proof.Blake2.X86.Stream.Update.len s₀)) s₃.mem := by rw [f₃.mem]; exact hcnt₂
    have hz₃ : isa.eval .e s₃ = some (decide (VG.Proof.Blake2.X86.Stream.Update.len s₀ - min (blockBytes w - r) (VG.Proof.Blake2.X86.Stream.Update.len s₀) = 0)) := by
      show s₃.zf = _
      rw [z₃, hptr₂.edi, BitVec.and_self, ofNat_beq_zero (by omega)]
    refine WP.ite _ hz₃ (fun hb' => ?_) (fun hb' => ?_)
    · simp only [decide_eq_true_eq] at hb'
      exact WP.block_nil ⟨_, _, hI₃, hptr₃, hcnt₃, .inl ⟨by omega, by omega⟩⟩
    · simp only [decide_eq_false_iff_not] at hb'
      have e : r + min (blockBytes w - r) (VG.Proof.Blake2.X86.Stream.Update.len s₀) = blockBytes w := by omega
      rw [e] at hI₃
      exact WP.mono (VG.Proof.Blake2.X86.Stream.Update.compressBuf_ok hP hf hp hI₃ hptr₃ hcnt₃) fun s₄ ⟨hI₄, hptr₄, hcnt₄⟩ =>
        ⟨_, _, hI₄, hptr₄, hcnt₄, .inr ⟨by omega, rfl⟩⟩

/-! ## `rest`: whole blocks straight from the data, and the last block -/

theorem ok_lg (hP : VG.Proof.Blake2.X86.Stream.Ok P) : 1 ≤ Nat.log2 (B w) ∧ Nat.log2 (B w) ≤ 31 ∧ 2 ^ Nat.log2 (B w) = blockBytes w := by
  rw [VG.Proof.Blake2.X86.Stream.B_eq]
  rcases hP.bb with h | h <;> rw [h]
  · rw [show (64 : Nat) = 2 ^ 6 from rfl, Nat.log2_two_pow]; decide
  · rw [show (128 : Nat) = 2 ^ 7 from rfl, Nat.log2_two_pow]; decide

theorem shr_ofNat (hP : VG.Proof.Blake2.X86.Stream.Ok P) {m : Nat} (h : m < 2 ^ 32) :
    BitVec.ofNat 32 m >>> Nat.log2 (B w) = BitVec.ofNat 32 (m / blockBytes w) := by
  obtain ⟨-, -, lgB⟩ := VG.Proof.Blake2.X86.Stream.Update.ok_lg hP
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h,
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) h), Nat.shiftRight_eq_div_pow, lgB]

/-- The blocks of data but the last, straight from the data. -/
theorem direct_ok (hP : VG.Proof.Blake2.X86.Stream.Ok P) {name : String} {code : Prog isa} (hf : VG.Proof.Blake2.X86.Stream.CalleeOk P code) {s₀ : State}
    (hp : VG.Proof.Blake2.X86.Stream.Update.Pre w s₀) {c : Nat} (hc : c < VG.Proof.Blake2.X86.Stream.Update.len s₀) {s : State} (hI : VG.Proof.Blake2.X86.Stream.Update.Inv P s₀ c 0 s) (hptr : VG.Proof.Blake2.X86.Stream.Update.Ptr s₀ c s)
    (hcnt : VG.Proof.Blake2.X86.Stream.Update.Cnt s₀ c s.mem) :
    WP isa (direct w name code) s fun s' =>
      VG.Proof.Blake2.X86.Stream.Update.Inv P s₀ (c + blockBytes w * ((VG.Proof.Blake2.X86.Stream.Update.len s₀ - c - 1) / blockBytes w)) 0 s' ∧
      VG.Proof.Blake2.X86.Stream.Update.Ptr s₀ (c + blockBytes w * ((VG.Proof.Blake2.X86.Stream.Update.len s₀ - c - 1) / blockBytes w)) s' := by
  have hl := hP.len
  have hL := VG.Proof.Blake2.X86.Stream.Update.len_lt s₀
  have hpos := hP.pos
  obtain ⟨lg₁, lg₂, -⟩ := VG.Proof.Blake2.X86.Stream.Update.ok_lg hP
  obtain ⟨k, hk⟩ : ∃ k, k = (VG.Proof.Blake2.X86.Stream.Update.len s₀ - c - 1) / blockBytes w := ⟨_, rfl⟩
  rw [← hk]
  have hdm := Nat.div_add_mod (VG.Proof.Blake2.X86.Stream.Update.len s₀ - c - 1) (blockBytes w)
  have hmod := Nat.mod_lt (VG.Proof.Blake2.X86.Stream.Update.len s₀ - c - 1) hpos
  rw [← hk] at hdm
  have hBk : blockBytes w * k ≤ VG.Proof.Blake2.X86.Stream.Update.len s₀ - c - 1 := by omega
  have hkle : k ≤ VG.Proof.Blake2.X86.Stream.Update.len s₀ - c - 1 := hk ▸ Nat.div_le_self _ _
  unfold direct
  refine WP.seq (wp_mov fun s₁ u₁ => wp_subi fun s₂ u₂ _ _ => wp_mov fun s₃ u₃ => wp_andi fun s₄ u₄ =>
    wp_sub fun s₅ u₅ z₅ => WP.block_nil ?_)
  have hL1 : s₂.gpr .eax = BitVec.ofNat 32 (VG.Proof.Blake2.X86.Stream.Update.len s₀ - c - 1) := by
    rw [u₂.gpr, u₁.gpr, hptr.edi, ofNat_pred (by omega)]
  have hcx₄ : s₄.gpr .ecx = BitVec.ofNat 32 ((VG.Proof.Blake2.X86.Stream.Update.len s₀ - c - 1) % blockBytes w) := by
    rw [u₄.gpr, u₃.gpr, hL1, VG.Proof.Blake2.X86.Stream.and_mask hP, toNat_ofNat_lt (by omega)]
  have hax₅ : s₅.gpr .eax = BitVec.ofNat 32 (blockBytes w * k) := by
    rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), hL1, hcx₄, sub_ofNat (by omega)]
    exact congrArg _ (by omega)
  have g₅ : ∀ x, x ≠ .eax → x ≠ .ecx → s₅.gpr x = s.gpr x := fun x h1 h2 => by
    rw [u₅.other x h1, u₄.other x h2, u₃.other x h2, u₂.other x h1, u₁.other x h1]
  have m₅ : s₅.mem = s.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have rd₅ : s₅.rd = s₀.rd := by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, hI.rd]
  have wr₅ : s₅.wr = s₀.wr := by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, hI.wr]
  have hz : isa.eval .e s₅ = some (decide (k = 0)) := by
    show s₅.zf = _
    rw [z₅, u₄.other _ (by decide), u₃.other _ (by decide), hL1, hcx₄, sub_ofNat (by omega),
      ofNat_beq_zero (by omega)]
    have : VG.Proof.Blake2.X86.Stream.Update.len s₀ - c - 1 - (VG.Proof.Blake2.X86.Stream.Update.len s₀ - c - 1) % blockBytes w = blockBytes w * k := by omega
    rw [this]
    simp only [Nat.mul_eq_zero, Nat.ne_of_gt hpos, false_or]
  have hcom : ∀ r ∈ [Reg.ebx, .ebp, .esp], s₅.gpr r = s.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact g₅ _ (by decide) (by decide)
  refine WP.ite _ hz (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    subst hb
    rw [Nat.mul_zero, Nat.add_zero]
    exact WP.block_nil ⟨hI.of_gpr hcom m₅ (by rw [rd₅, hI.rd]) (by rw [wr₅, hI.wr]),
      hptr.of_gpr (g₅ _ (by decide) (by decide)) (g₅ _ (by decide) (by decide))⟩
  simp only [decide_eq_false_iff_not] at hb
  have hk1 : 1 ≤ k := Nat.pos_of_ne_zero hb
  have hB1 : blockBytes w ≤ blockBytes w * k := Nat.le_mul_of_pos_right _ hk1
  have bp₅ : s₅.gpr .ebp = VG.Proof.Blake2.X86.Stream.Update.scr s₀ := by rw [g₅ _ (by decide) (by decide), hI.ebp]
  refine WP.seq (wp_stm (o := lenOff) bp₅ (hp.sin wr₅ (by decide)) fun s₆ u₆ => ?_)
  refine wp_stm (o := bytesOff) (by rw [u₆.gpr, bp₅]) (by rw [u₆.wr]; exact hp.sin wr₅ (by decide))
    fun s₇ u₇ => ?_
  refine wp_mov fun s₈ u₈ => wp_shr ⟨lg₁, lg₂⟩ fun s₉ u₉ _ => ?_
  have bp₉ : s₉.gpr .ebp = VG.Proof.Blake2.X86.Stream.Update.scr s₀ := by rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr, u₆.gpr, bp₅]
  have rd₉ : s₉.rd = s₀.rd := by rw [u₉.rd, u₈.rd, u₇.rd, u₆.rd, rd₅]
  have wr₉ : s₉.wr = s₀.wr := by rw [u₉.wr, u₈.wr, u₇.wr, u₆.wr, wr₅]
  have m₉ : s₉.mem = (s.mem.writeW (addr (VG.Proof.Blake2.X86.Stream.Update.scr s₀) lenOff) (s₅.gpr .edi)).writeW (addr (VG.Proof.Blake2.X86.Stream.Update.scr s₀) bytesOff)
      (BitVec.ofNat 32 (blockBytes w * k)) := by
    rw [u₉.mem, u₈.mem, u₇.mem, u₆.gpr, u₆.mem, hax₅, m₅]
  have rdlo : s₉.mem.readW (addr (VG.Proof.Blake2.X86.Stream.Update.scr s₀) cloOff) 32 = BitVec.ofNat 32 (VG.Proof.Blake2.X86.Stream.Update.cnt s₀ + c) := by
    rw [m₉, VG.Proof.Blake2.X86.Stream.rw_scr hp.scr_fit _ _ (by decide) (by decide) (by decide),
      VG.Proof.Blake2.X86.Stream.rw_scr hp.scr_fit _ _ (by decide) (by decide) (by decide), hcnt.lo]
  have rdhi : s₉.mem.readW (addr (VG.Proof.Blake2.X86.Stream.Update.scr s₀) chiOff) 32 = BitVec.ofNat 32 ((VG.Proof.Blake2.X86.Stream.Update.cnt s₀ + c) / 2 ^ 32) := by
    rw [m₉, VG.Proof.Blake2.X86.Stream.rw_scr hp.scr_fit _ _ (by decide) (by decide) (by decide),
      VG.Proof.Blake2.X86.Stream.rw_scr hp.scr_fit _ _ (by decide) (by decide) (by decide), hcnt.hi]
  refine VG.Proof.Blake2.X86.Stream.wp_ldmF bp₉ (hp.sinr rd₉ wr₉ (d := cloOff) (by decide)) fun s₁₀ u₁₀ _ _ => ?_
  refine VG.Proof.Blake2.X86.Stream.wp_addiC fun s₁₁ u₁₁ cf₁₁ => ?_
  have ichi := hp.sinr rd₉ wr₉ (d := chiOff) (by decide)
  refine VG.Proof.Blake2.X86.Stream.wp_ldmF (by rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), bp₉])
    (by rw [u₁₁.rd, u₁₁.wr, u₁₀.rd, u₁₀.wr]; exact ichi) fun s₁₂ u₁₂ cf₁₂ _ => ?_
  refine VG.Proof.Blake2.X86.Stream.wp_adc0 (by rw [cf₁₂, cf₁₁]) fun s₁₃ u₁₃ => wp_movi fun s₁₄ u₁₄ => WP.block_nil ?_
  have g₁₄ : ∀ x, x ≠ .eax → x ≠ .ecx → x ≠ .edx → x ≠ .edi → s₁₄.gpr x = s.gpr x := fun x h1 h2 h3 h4 => by
    rw [u₁₄.other x h1, u₁₃.other x h3, u₁₂.other x h3, u₁₁.other x h2, u₁₀.other x h2, u₉.other x h4,
      u₈.other x h4, u₇.gpr, u₆.gpr, g₅ x h1 h2]
  have m₁₄ : s₁₄.mem = s₉.mem := by rw [u₁₄.mem, u₁₃.mem, u₁₂.mem, u₁₁.mem, u₁₀.mem]
  have lo₁₁ : s₁₁.gpr .ecx = BitVec.ofNat 32 (VG.Proof.Blake2.X86.Stream.Update.cnt s₀ + c + blockBytes w) := by
    rw [u₁₁.gpr, u₁₀.gpr, rdlo, VG.Proof.Blake2.X86.Stream.B_eq, ← BitVec.ofNat_add]
  have sv₉ := Saved.write hp (Saved.write hp hI.saved (d := lenOff) (by decide) (by decide) (s₅.gpr .edi))
    (d := bytesOff) (by decide) (by decide) (BitVec.ofNat 32 (blockBytes w * k))
  have hC₁₄ : VG.Proof.Blake2.X86.Stream.Update.Common w s₀ c s₁₄ :=
    ⟨hI.c_le, by rw [u₁₄.rd, u₁₃.rd, u₁₂.rd, u₁₁.rd, u₁₀.rd, rd₉],
      by rw [u₁₄.wr, u₁₃.wr, u₁₂.wr, u₁₁.wr, u₁₀.wr, wr₉],
      by rw [g₁₄ _ (by decide) (by decide) (by decide) (by decide), hI.ebx],
      by rw [g₁₄ _ (by decide) (by decide) (by decide) (by decide), hI.ebp],
      by rw [g₁₄ _ (by decide) (by decide) (by decide) (by decide), hI.esp],
      by rw [m₁₄, m₉]; exact VG.Proof.Blake2.X86.Stream.Update.frame_scr hp (VG.Proof.Blake2.X86.Stream.Update.frame_scr hp hI.frame (by decide) _) (by decide) _,
      by rw [m₁₄, m₉]; exact sv₉⟩
  have hdi₁₄ : s₁₄.gpr .edi = BitVec.ofNat 32 k := by
    rw [u₁₄.other _ (by decide), u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₁.other _ (by decide),
      u₁₀.other _ (by decide), u₉.gpr, u₈.gpr, u₇.gpr, u₆.gpr, hax₅, VG.Proof.Blake2.X86.Stream.Update.shr_ofNat hP (by omega),
      Nat.mul_div_cancel_left _ hpos]
  have hdx₁₄ : s₁₄.gpr .edx = BitVec.ofNat 32 ((VG.Proof.Blake2.X86.Stream.Update.cnt s₀ + c + blockBytes w) / 2 ^ 32) := by
    rw [u₁₄.other _ (by decide), u₁₃.gpr, u₁₂.gpr, u₁₁.mem, u₁₀.mem, rdhi, u₁₀.gpr, rdlo, VG.Proof.Blake2.X86.Stream.B_eq,
      VG.Proof.Blake2.X86.Stream.carry_ofNat _ _ (by omega)]
  refine WP.seq (VG.Proof.Blake2.X86.Stream.Update.call_upd hP hf hp (blk := VG.Proof.Blake2.X86.Stream.Update.dp s₀ + BitVec.ofNat 32 c) (k := k)
    (tlo := BitVec.ofNat 32 (VG.Proof.Blake2.X86.Stream.Update.cnt s₀ + c + blockBytes w))
    (thi := BitVec.ofNat 32 ((VG.Proof.Blake2.X86.Stream.Update.cnt s₀ + c + blockBytes w) / 2 ^ 32)) hC₁₄.rd hC₁₄.wr hC₁₄.esp hC₁₄.ebx hC₁₄.ebp
    (by rw [g₁₄ _ (by decide) (by decide) (by decide) (by decide), hptr.esi])
    (by rw [hdi₁₄, toNat_ofNat_lt (by omega)])
    (by rw [u₁₄.other _ (by decide), u₁₃.other _ (by decide), u₁₂.other _ (by decide), lo₁₁]) hdx₁₄
    u₁₄.gpr (.inr ⟨c, rfl, by omega, hk1⟩) fun s' rd' wr' cs' f' post => ?_)
  have hC' : VG.Proof.Blake2.X86.Stream.Update.Common w s₀ c s' := hC₁₄.after_call hP hp rd' wr' cs' f'
  have kc : ∀ d, 512 ≤ d → d + 4 ≤ 576 → s'.mem.readW (addr (VG.Proof.Blake2.X86.Stream.Update.scr s₀) d) 32 = s₁₄.mem.readW (addr (VG.Proof.Blake2.X86.Stream.Update.scr s₀) d) 32 :=
    fun _ h₁ h₂ => VG.Proof.Blake2.X86.Stream.Update.keep_call hp f' h₁ h₂
  refine wp_ldm (b := .ebp) hC'.ebp (hp.sinr hC'.rd hC'.wr (d := bytesOff) (by decide)) fun s₁₅ u₁₅ => ?_
  refine wp_add fun s₁₆ u₁₆ _ => ?_
  have ilen := hp.sinr hC'.rd hC'.wr (d := lenOff) (by decide)
  refine wp_ldm (b := .ebp) (by rw [u₁₆.other _ (by decide), u₁₅.other _ (by decide), hC'.ebp])
    (by rw [u₁₆.rd, u₁₆.wr, u₁₅.rd, u₁₅.wr]; exact ilen) fun s₁₇ u₁₇ => ?_
  refine wp_sub fun s₁₈ u₁₈ _ => WP.block_nil ?_
  have ax₁₅ : s₁₅.gpr .eax = BitVec.ofNat 32 (blockBytes w * k) := by
    rw [u₁₅.gpr, kc bytesOff (by decide) (by decide), m₁₄, m₉, Mem.readW_writeW_self32]
  have g₁₈ : ∀ x, x ≠ .eax → x ≠ .esi → x ≠ .edi → s₁₈.gpr x = s'.gpr x := fun x h1 h2 h3 => by
    rw [u₁₈.other x h3, u₁₇.other x h3, u₁₆.other x h2, u₁₅.other x h1]
  have m₁₈ : s₁₈.mem = s'.mem := by rw [u₁₈.mem, u₁₇.mem, u₁₆.mem, u₁₅.mem]
  have hC₁₈ : VG.Proof.Blake2.X86.Stream.Update.Common w s₀ c s₁₈ := hC'.of_gpr (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact g₁₈ _ (by decide) (by decide) (by decide)) m₁₈
    (by rw [u₁₈.rd, u₁₇.rd, u₁₆.rd, u₁₅.rd]) (by rw [u₁₈.wr, u₁₇.wr, u₁₆.wr, u₁₅.wr])
  refine ⟨⟨{ hC₁₈ with c_le := by omega }, fun h0 d hd => ?_⟩, ⟨?_, ?_⟩⟩
  · have hcn := hd.cnt_eq
    have hlt := hd.2.2
    have hst : ∀ i < bufOff w + blockBytes w,
        s₁₄.mem (VG.Proof.Blake2.X86.Stream.Update.stA s₀ + BitVec.ofNat 64 i) = s.mem (VG.Proof.Blake2.X86.Stream.Update.stA s₀ + BitVec.ofNat 64 i) := by
      refine VG.Proof.Blake2.X86.Stream.Update.st_keep hP hp ?_
      rw [m₁₄, m₉]
      exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (hp.scr_in (by decide))).writeW
        (List.mem_singleton_self _) _ (hp.scr_in (by decide))
    have e : d ++ VG.Proof.Blake2.X86.Stream.Update.D s₀ (c + blockBytes w * k) =
        d ++ VG.Proof.Blake2.X86.Stream.Update.D s₀ c ++ VG.Spec.Blake2.bytesAt s₁₄.mem (VG.Proof.Blake2.X86.Stream.Update.dA s₀ + BitVec.ofNat 64 c) (blockBytes w * k) := by
      rw [VG.Proof.Blake2.X86.Stream.Update.D, bytesAt_add, List.append_assoc]
      refine congrArg (fun l => d ++ (VG.Spec.Blake2.bytesAt s₀.mem (VG.Proof.Blake2.X86.Stream.Update.dA s₀) c ++ l)) (bytesAt_congr fun i hi => ?_)
      rw [Offset.add_add]
      exact (hC₁₄.data hp (by omega)).symm
    rw [m₁₈, e]
    refine reprR_blocks P hpos (VG.Proof.Blake2.X86.Stream.reprR_congr hP hst (hI.repr h0 d hd)) ?_
    rw [post, VG.Proof.Blake2.X86.Stream.Update.dp_add hp hc, VG.Proof.Blake2.X86.Stream.append_ofNat (by omega), List.length_append, VG.Proof.Blake2.X86.Stream.Update.D_length, ← hcn]
  · rw [u₁₈.other _ (by decide), u₁₇.other _ (by decide), u₁₆.gpr, u₁₅.other _ (by decide), ax₁₅,
      cs' _ (by decide), g₁₄ _ (by decide) (by decide) (by decide) (by decide), hptr.esi, BitVec.add_assoc,
      BitVec.ofNat_add]
  · rw [u₁₈.gpr, u₁₇.gpr, u₁₇.other .eax (by decide), u₁₆.other .eax (by decide), ax₁₅, u₁₆.mem, u₁₅.mem,
      kc lenOff (by decide) (by decide),
      m₁₄, m₉, VG.Proof.Blake2.X86.Stream.rw_scr hp.scr_fit _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32,
      g₅ _ (by decide) (by decide), hptr.edi, sub_ofNat (by omega)]
    exact congrArg _ (by omega)

/-- The last `1` to `B` bytes of data, into the empty buffer. -/
theorem tail_ok (hP : VG.Proof.Blake2.X86.Stream.Ok P) {s₀ : State} (hp : VG.Proof.Blake2.X86.Stream.Update.Pre w s₀) {c : Nat} (hc₁ : c < VG.Proof.Blake2.X86.Stream.Update.len s₀)
    (hc₂ : VG.Proof.Blake2.X86.Stream.Update.len s₀ - c ≤ blockBytes w) {s : State} (hI : VG.Proof.Blake2.X86.Stream.Update.Inv P s₀ c 0 s) (hptr : VG.Proof.Blake2.X86.Stream.Update.Ptr s₀ c s) :
    WP isa (tail w) s (VG.Proof.Blake2.X86.Stream.Update.Inv P s₀ (VG.Proof.Blake2.X86.Stream.Update.len s₀) (VG.Proof.Blake2.X86.Stream.Update.len s₀ - c)) := by
  have hL := VG.Proof.Blake2.X86.Stream.Update.len_lt s₀
  unfold tail
  refine WP.seq (wp_mov fun s₁ u₁ => wp_mov fun s₂ u₂ => WP.block_nil ?_)
  have hg : ∀ x, x ≠ .ecx → x ≠ .edx → s₂.gpr x = s.gpr x := fun x h1 h2 => by
    rw [u₂.other x h2, u₁.other x h1]
  have hm₂ : s₂.mem = s.mem := by rw [u₂.mem, u₁.mem]
  refine WP.mono (VG.Proof.Blake2.X86.Stream.Update.copy_ok hP hp (c := c) (r := 0) (k := VG.Proof.Blake2.X86.Stream.Update.len s₀ - c) (by omega) (by omega) (by omega)
      (by rw [u₂.rd, u₁.rd, hI.rd]) (by rw [u₂.wr, u₁.wr, hI.wr])
      (by rw [hg _ (by decide) (by decide)]; exact hptr.esi)
      (by rw [u₂.gpr, u₁.other _ (by decide), hI.ebx]; simp)
      (by rw [u₂.other _ (by decide), u₁.gpr, hptr.edi])
      (by rw [hm₂]; exact hI.frame) (by rw [hm₂]; exact hI.repr))
    fun s₃ ⟨g₃, _, rd₃, wr₃, f₃, rp₃⟩ => ?_
  have e : c + (VG.Proof.Blake2.X86.Stream.Update.len s₀ - c) = VG.Proof.Blake2.X86.Stream.Update.len s₀ := by omega
  rw [e, Nat.zero_add] at rp₃
  have g : ∀ x, x ≠ .esi → x ≠ .edx → x ≠ .ecx → x ≠ .eax → s₃.gpr x = s.gpr x := fun x h1 h2 h3 h4 => by
    rw [g₃ x h1 h2 h3 h4, hg x h3 h2]
  refine ⟨⟨Nat.le_refl _, rd₃, wr₃, ?_, ?_, ?_, ?_, ?_⟩, rp₃⟩
  · rw [g _ (by decide) (by decide) (by decide) (by decide)]; exact hI.ebx
  · rw [g _ (by decide) (by decide) (by decide) (by decide)]; exact hI.ebp
  · rw [g _ (by decide) (by decide) (by decide) (by decide)]; exact hI.esp
  · exact VG.Proof.Blake2.X86.Stream.Update.frame_st hI.frame (by rw [← hm₂]; exact f₃)
  · exact Saved.st hp hI.saved (by rw [← hm₂]; exact f₃)

/-- All the data is in, and the buffer is not empty. -/
def Full (P : VG.Spec.Blake2.Params w) (s₀ : State) (s : State) : Prop := ∃ r, VG.Proof.Blake2.X86.Stream.Update.Inv P s₀ (VG.Proof.Blake2.X86.Stream.Update.len s₀) r s ∧ 1 ≤ r

theorem rest_ok (hP : VG.Proof.Blake2.X86.Stream.Ok P) {name : String} {code : Prog isa} (hf : VG.Proof.Blake2.X86.Stream.CalleeOk P code) {s₀ : State}
    (hp : VG.Proof.Blake2.X86.Stream.Update.Pre w s₀) {s : State} (h : VG.Proof.Blake2.X86.Stream.Update.HeadPost P s₀ s) : WP isa (rest w name code) s (VG.Proof.Blake2.X86.Stream.Update.Full P s₀) := by
  have hL := VG.Proof.Blake2.X86.Stream.Update.len_lt s₀
  have hpos := hP.pos
  obtain ⟨c, r, hI, hptr, hcnt, hcr⟩ := h
  unfold rest
  refine WP.seq (wp_test fun s₁ f₁ z₁ => WP.block_nil ?_)
  have hI₁ := hI.of_gpr (fun r _ => by rw [f₁.gpr]) f₁.mem f₁.rd f₁.wr
  have hptr₁ := hptr.of_gpr (by rw [f₁.gpr]) (by rw [f₁.gpr])
  have hz : isa.eval .e s₁ = some (decide (VG.Proof.Blake2.X86.Stream.Update.len s₀ - c = 0)) := by
    show s₁.zf = _
    rw [z₁, hptr.edi, BitVec.and_self, ofNat_beq_zero (by omega)]
  have hc := hI.c_le
  refine WP.ite _ hz (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    rcases hcr with ⟨rfl, hr⟩ | ⟨hc', _⟩
    · exact WP.block_nil ⟨r, hI₁, hr⟩
    · omega
  · simp only [decide_eq_false_iff_not] at hb
    rcases hcr with ⟨rfl, hr⟩ | ⟨hc', rfl⟩
    · omega
    refine WP.seq (WP.mono (VG.Proof.Blake2.X86.Stream.Update.direct_ok hP hf hp hc' hI₁ hptr₁ (by rw [f₁.mem]; exact hcnt))
      fun s₂ ⟨hI₂, hptr₂⟩ => ?_)
    have hdm := Nat.div_add_mod (VG.Proof.Blake2.X86.Stream.Update.len s₀ - c - 1) (blockBytes w)
    have hmod := Nat.mod_lt (VG.Proof.Blake2.X86.Stream.Update.len s₀ - c - 1) hpos
    exact WP.mono (VG.Proof.Blake2.X86.Stream.Update.tail_ok hP hp (by omega) (by omega) hI₂ hptr₂) fun s₃ hI₃ => ⟨_, hI₃, by omega⟩

/-! ## Epilogue and the whole function -/

/-- All the data is in. -/
def Done (P : VG.Spec.Blake2.Params w) (s₀ : State) (s : State) : Prop :=
  VG.Proof.Blake2.X86.Stream.Update.Common w s₀ (VG.Proof.Blake2.X86.Stream.Update.len s₀) s ∧
    ∀ h0 d, VG.Proof.Blake2.X86.Stream.Update.R₀ P s₀ h0 d → Spec.Blake2.Repr P h0 s.mem (VG.Proof.Blake2.X86.Stream.Update.stA s₀) (d ++ VG.Proof.Blake2.X86.Stream.Update.D s₀ (VG.Proof.Blake2.X86.Stream.Update.len s₀))

theorem Full.done (hP : VG.Proof.Blake2.X86.Stream.Ok P) {s₀ : State} {s : State} (h : VG.Proof.Blake2.X86.Stream.Update.Full P s₀ s) : VG.Proof.Blake2.X86.Stream.Update.Done P s₀ s := by
  obtain ⟨r, hI, hr⟩ := h
  exact ⟨hI.toCommon, fun h0 d hd => repr_of_reprR P hP.pos (hI.repr h0 d hd) hr⟩

theorem epilogue_ok {s₀ : State} (hp : VG.Proof.Blake2.X86.Stream.Update.Pre w s₀) {s : State} (hD : VG.Proof.Blake2.X86.Stream.Update.Done P s₀ s) :
    WP isa (.block restore) s fun s' => abiPreserved s₀ s' ∧ (updateX86 P).post s₀ s' := by
  obtain ⟨hC, hrepr⟩ := hD
  refine WP.mono (VG.Proof.Blake2.X86.Stream.restore_saved hC.ebp (fun d _ hd => hp.sinr hC.rd hC.wr (by omega)) hC.saved)
    fun s₅ ⟨hg, hsp, hm₅⟩ => ?_
  refine ⟨⟨fun r hr => ?_, ?_⟩, fun h0 d hd hc hl => ?_⟩
  · by_cases h : r = .esp
    · subst h; rw [hsp, hC.esp]
    · exact hg r hr h
  · rw [hm₅]
    refine hC.frame.readW (r := VG.Proof.Blake2.X86.Stream.Update.retR s₀) (Region.contains_self _ _) ?_ (by decide)
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    exacts [hp.ret_st, hp.ret_scr, hp.ret_stk]
  · rw [hm₅]; exact hrepr h0 d ⟨hd, hc, hl⟩

theorem correct (hP : VG.Proof.Blake2.X86.Stream.Ok P) {name : String} {code : Prog isa} (hf : VG.Proof.Blake2.X86.Stream.CalleeOk P code) {s₀ : State}
    (hp : VG.Proof.Blake2.X86.Stream.Update.Pre w s₀) :
    WP isa (update w name code) s₀ fun s' => abiPreserved s₀ s' ∧ (updateX86 P).post s₀ s' := by
  have hL := VG.Proof.Blake2.X86.Stream.Update.len_lt s₀
  unfold update
  refine WP.seq (WP.mono (VG.Proof.Blake2.X86.Stream.Update.prologue_ok hp) fun s₁ ⟨hC, hptr, hm, hax, hcx⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Blake2.X86.Stream.Update.bufLen_ok hP hp hC hptr hm hax hcx) fun s₂ ⟨hI, hptr₂, hcnt₂, hax₂⟩ => ?_)
  refine WP.seq (wp_test fun s₃ f₃ z₃ => WP.block_nil ?_)
  have hI₃ := hI.of_gpr (fun r _ => by rw [f₃.gpr]) f₃.mem f₃.rd f₃.wr
  have hptr₃ := hptr₂.of_gpr (by rw [f₃.gpr]) (by rw [f₃.gpr])
  refine WP.seq (WP.mono (Q := VG.Proof.Blake2.X86.Stream.Update.Done P s₀) ?_ fun s₄ h => VG.Proof.Blake2.X86.Stream.Update.epilogue_ok hp h)
  have hz : isa.eval .e s₃ = some (decide (VG.Proof.Blake2.X86.Stream.Update.len s₀ = 0)) := by
    show s₃.zf = _
    rw [z₃, hptr₂.edi, BitVec.and_self, Nat.sub_zero, ofNat_beq_zero (by omega)]
  refine WP.ite _ hz (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    refine WP.block_nil ⟨{ hI₃.toCommon with c_le := by omega }, fun h0 d hd => ?_⟩
    have := hI₃.repr h0 d hd
    have e0 : ∀ n, n = 0 → VG.Proof.Blake2.X86.Stream.Update.D s₀ n = [] := by rintro _ rfl; simp [VG.Spec.Blake2.bytesAt]
    rw [e0 0 rfl, List.append_nil] at this
    rw [e0 _ hb, List.append_nil, repr_iff P hP.pos, ← hd.cnt_eq]; exact this
  · simp only [decide_eq_false_iff_not] at hb
    have hr := bufLen_le (w := w) hP.pos (VG.Proof.Blake2.X86.Stream.Update.cnt s₀)
    exact WP.seq (WP.mono (VG.Proof.Blake2.X86.Stream.Update.head_ok hP hf hp hr (by omega) hI₃ hptr₃ (by rw [f₃.mem]; exact hcnt₂)
      (by rw [f₃.gpr]; exact hax₂)) fun s₄ h => WP.mono (VG.Proof.Blake2.X86.Stream.Update.rest_ok hP hf hp h) fun s₅ h => h.done hP)

end VG.Proof.Blake2.X86.Stream.Update

end

/- Proofs formerly in `VerifiedGarbage.Proof.Blake2.X86.Stream.Verified`. -/
section

/-!
# Streaming BLAKE2 on x86 (32-bit): `Verified`, for any compression function

`init`, `update` and `finalize` meet the per-target contracts of
`Proof/Blake2/X86/Contract.lean`, for either word size, given a correct
compression function (`CalleeOk`) and that the code (with that compression
function) is constant time, which each instance proves by the taint analysis
(`VG.Taint.constantTime`) from the initial taint (`τInit`, `τUpdate`,
`τFinalize`) and the facts that the public inputs give it (`init_agree`,
`update_agree`, `finalize_agree`).
-/

namespace VG.Proof.Blake2.X86.Stream

open VG VG.X86 VG.Spec.Blake2
open VG.Proof.Blake2 (initX86 updateX86 finalizeX86)

variable {w : Nat} {P : VG.Spec.Blake2.Params w}

/-! ## The initial taint -/

section
variable (w : Nat)

/-- `init`: the stack arguments are public, and the word holding `state` is
the base address of the writable region. -/
def τInit : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [bufOff w + blockBytes w], argLen := 20,
    argBases := [(4, 0)] }

/-- `update`: the stack arguments are public, the words holding `state` and
`scratch` are the base addresses of the writable regions, and the 32 bytes
below `esp` are outside them. -/
def τUpdate : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [bufOff w + blockBytes w, 576], argLen := 28,
    argBases := [(4, 0), (24, 1)], room := 32 }

/-- `finalize`: as `update`, with the output. -/
def τFinalize : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [bufOff w + blockBytes w, bufOff w, 576], argLen := 24,
    argBases := [(4, 0), (16, 1), (20, 2)], room := 32 }

end

theorem argMem_eq {s₁ s₂ : State} {n : Nat} (f₁ : (s₁.gpr .esp).toNat + n ≤ 2 ^ 32)
    (f₂ : (s₂.gpr .esp).toNat + n ≤ 2 ^ 32) (ha : ∀ i, 4 + 4 * i < n → VG.X86.arg s₁ i = VG.X86.arg s₂ i) {k : Nat}
    (h4 : 4 ≤ k) (hk : k < n) :
    s₁.mem (VG.X86.Taint.argByte s₁ (VG.X86.Taint.depth ([] : List (Option Nat)) + k)) =
      s₂.mem (VG.X86.Taint.argByte s₂ (VG.X86.Taint.depth ([] : List (Option Nat)) + k)) := by
  rw [show VG.X86.Taint.depth ([] : List (Option Nat)) = 0 from rfl, Nat.zero_add,
    VG.X86.Taint.argByte_eq f₁ h4 hk, VG.X86.Taint.argByte_eq f₂ h4 hk,
    Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by omega)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by omega))]
  exact congrArg _ (ha _ (by omega))

/-! ## `init` -/

theorem init_wf (hP : VG.Proof.Blake2.X86.Stream.Ok P) {s : State} (h : (initX86 P).pre s) : VG.X86.Taint.Wf (VG.Proof.Blake2.X86.Stream.τInit w) s := by
  have hp := Init.pre_of h
  have hst := hp.st_fit; have hs := hp.sp_fit; have hl := hP.len
  refine VG.X86.Taint.Wf.entry rfl rfl ⟨fun _ => ⟨by simp [hp.wr, VG.Proof.Blake2.X86.Stream.τInit], by simp [hp.wr], ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨by simp only [VG.Proof.Blake2.X86.Stream.τInit]; omega, ?_⟩, ?_⟩
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r rfl; simp only [BitVec.toNat_setWidth]; omega
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r rfl
    exact VG.X86.Taint.frame_disjoint (n := 16) (by omega) hp.ret_st hp.a_st
  · intro p hp'
    simp only [VG.Proof.Blake2.X86.Stream.τInit, List.mem_cons, List.not_mem_nil, or_false] at hp'
    subst hp'
    exact ⟨by simp [VG.Proof.Blake2.X86.Stream.τInit], by simp [VG.X86.Taint.region, hp.wr, addr, VG.X86.arg, argAddr]⟩

theorem init_agree (hP : VG.Proof.Blake2.X86.Stream.Ok P) {s₁ s₂ : State} (h₁ : (initX86 P).pre s₁) (h₂ : (initX86 P).pre s₂)
    (hpub : (initX86 P).pub s₁ s₂) : VG.X86.Taint.Agree (VG.Proof.Blake2.X86.Stream.τInit w) s₁ s₂ := by
  obtain ⟨hesp, ha⟩ := hpub
  have hp₁ := Init.pre_of h₁; have hp₂ := Init.pre_of h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, VG.Proof.Blake2.X86.Stream.init_wf hP h₁, VG.Proof.Blake2.X86.Stream.init_wf hP h₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => hesp,
    fun k h4 hk => VG.Proof.Blake2.X86.Stream.argMem_eq (n := 20) (by have := hp₁.sp_fit; omega) (by have := hp₂.sp_fit; omega)
      (fun i hi => ha i (by omega)) h4 hk⟩
  · simp only [VG.Proof.Blake2.X86.Stream.τInit, RegSet.mem_ofList, List.mem_singleton] at hr
    subst hr; exact hesp
  · rw [hp₁.wr, hp₂.wr]
    simp only [Init.stR, Init.stA, Init.st, ha 0 (by omega)]

/-! ## `update` -/

theorem update_wf (hP : VG.Proof.Blake2.X86.Stream.Ok P) {s : State} (h : (updateX86 P).pre s) : VG.X86.Taint.Wf (VG.Proof.Blake2.X86.Stream.τUpdate w) s := by
  have hp := Update.pre_of h
  have hst := hp.st_fit; have hsc := hp.scr_fit; have hs := hp.sp_fit
  have hlo := hp.sp_lo; have hl := hP.len
  obtain ⟨-, -, -, -, -, -, -, -, -, k1, k2, -⟩ := h
  refine VG.X86.Taint.Wf.entryRoom rfl ⟨fun _ => ⟨by simp [hp.wr, VG.Proof.Blake2.X86.Stream.τUpdate], ?_, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨by simp only [VG.Proof.Blake2.X86.Stream.τUpdate]; omega, ?_⟩, ?_⟩ fun _ => ⟨hlo, ?_⟩
  · simp only [hp.wr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq,
      List.Pairwise.nil, and_true]
    exact ⟨hp.st_scr, fun _ h => h.elim⟩
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [BitVec.toNat_setWidth] <;> omega
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact VG.X86.Taint.frame_disjoint (n := 24) (by omega) hp.ret_st hp.a_st
    · exact VG.X86.Taint.frame_disjoint (n := 24) (by omega) hp.ret_scr hp.a_scr
  · intro p hp'
    simp only [VG.Proof.Blake2.X86.Stream.τUpdate, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl <;> refine ⟨by simp [VG.Proof.Blake2.X86.Stream.τUpdate], ?_⟩ <;>
      simp [VG.X86.Taint.region, hp.wr, addr, VG.X86.arg, argAddr]
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    exacts [k1, k2]

theorem update_agree (hP : VG.Proof.Blake2.X86.Stream.Ok P) {s₁ s₂ : State} (h₁ : (updateX86 P).pre s₁) (h₂ : (updateX86 P).pre s₂)
    (hpub : (updateX86 P).pub s₁ s₂) : VG.X86.Taint.Agree (VG.Proof.Blake2.X86.Stream.τUpdate w) s₁ s₂ := by
  obtain ⟨hesp, ha⟩ := hpub
  have hp₁ := Update.pre_of h₁; have hp₂ := Update.pre_of h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, VG.Proof.Blake2.X86.Stream.update_wf hP h₁, VG.Proof.Blake2.X86.Stream.update_wf hP h₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => hesp,
    fun k h4 hk => VG.Proof.Blake2.X86.Stream.argMem_eq (n := 28) hp₁.sp_fit hp₂.sp_fit (fun i hi => ha i (by omega)) h4 hk⟩
  · simp only [VG.Proof.Blake2.X86.Stream.τUpdate, RegSet.mem_ofList, List.mem_singleton] at hr
    subst hr; exact hesp
  · rw [hp₁.wr, hp₂.wr]
    simp only [Update.stR, Update.scR, Update.stA, Update.scA, Update.st, Update.scr, ha 0 (by omega),
      ha 5 (by omega)]

/-! ## `finalize` -/

theorem finalize_wf (hP : VG.Proof.Blake2.X86.Stream.Ok P) {s : State} (h : (finalizeX86 P).pre s) :
    VG.X86.Taint.Wf (VG.Proof.Blake2.X86.Stream.τFinalize w) s := by
  have hp := Finalize.pre_of h
  have hst := hp.st_fit; have hso := hp.out_fit; have hsc := hp.scr_fit; have hs := hp.sp_fit
  have hlo := hp.sp_lo; have hl := hP.len
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, k1, k2, k3, -⟩ := h
  refine VG.X86.Taint.Wf.entryRoom rfl ⟨fun _ => ⟨by simp [hp.wr, VG.Proof.Blake2.X86.Stream.τFinalize], ?_, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨by simp only [VG.Proof.Blake2.X86.Stream.τFinalize]; omega, ?_⟩, ?_⟩ fun _ => ⟨hlo, ?_⟩
  · simp only [hp.wr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, List.Pairwise.nil, and_true]
    exact ⟨⟨hp.st_out, hp.st_scr⟩, hp.out_scr, fun _ h => h.elim⟩
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl) <;> simp only [BitVec.toNat_setWidth] <;> omega
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact VG.X86.Taint.frame_disjoint (n := 20) (by omega) hp.ret_st hp.a_st
    · exact VG.X86.Taint.frame_disjoint (n := 20) (by omega) hp.ret_out hp.a_out
    · exact VG.X86.Taint.frame_disjoint (n := 20) (by omega) hp.ret_scr hp.a_scr
  · intro p hp'
    simp only [VG.Proof.Blake2.X86.Stream.τFinalize, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl | rfl <;> refine ⟨by simp [VG.Proof.Blake2.X86.Stream.τFinalize], ?_⟩ <;>
      simp [VG.X86.Taint.region, hp.wr, addr, VG.X86.arg, argAddr]
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    exacts [k1, k2, k3]

theorem finalize_agree (hP : VG.Proof.Blake2.X86.Stream.Ok P) {s₁ s₂ : State} (h₁ : (finalizeX86 P).pre s₁)
    (h₂ : (finalizeX86 P).pre s₂) (hpub : (finalizeX86 P).pub s₁ s₂) :
    VG.X86.Taint.Agree (VG.Proof.Blake2.X86.Stream.τFinalize w) s₁ s₂ := by
  obtain ⟨hesp, ha⟩ := hpub
  have hp₁ := Finalize.pre_of h₁; have hp₂ := Finalize.pre_of h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, VG.Proof.Blake2.X86.Stream.finalize_wf hP h₁, VG.Proof.Blake2.X86.Stream.finalize_wf hP h₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => hesp,
    fun k h4 hk => VG.Proof.Blake2.X86.Stream.argMem_eq (n := 24) hp₁.sp_fit hp₂.sp_fit (fun i hi => ha i (by omega)) h4 hk⟩
  · simp only [VG.Proof.Blake2.X86.Stream.τFinalize, RegSet.mem_ofList, List.mem_singleton] at hr
    subst hr; exact hesp
  · rw [hp₁.wr, hp₂.wr]
    simp only [Finalize.stR, Finalize.outR, Finalize.scR, Finalize.stA, Finalize.opA, Finalize.scA,
      Finalize.st, Finalize.op, Finalize.scr, ha 0 (by omega), ha 3 (by omega), ha 4 (by omega)]

/-! ## `Verified` -/

theorem init_verified (hP : VG.Proof.Blake2.X86.Stream.Ok P)
    (hct : ConstantTime isa (initX86 P).pre (initX86 P).pub (Impl.Blake2.X86.Stream.init P))
    (hsat : ∃ s, (initX86 P).pre s) :
    Verified X86.target (Impl.Blake2.X86.Stream.init P) (initX86 P) :=
  ⟨fun _ hs => Init.correct hP (Init.pre_of hs), hct, hsat⟩

theorem update_verified (hP : VG.Proof.Blake2.X86.Stream.Ok P) {name : String} {code : Prog isa} (hf : VG.Proof.Blake2.X86.Stream.CalleeOk P code)
    (hct : ConstantTime isa (updateX86 P).pre (updateX86 P).pub (Impl.Blake2.X86.Stream.update w name code))
    (hsat : ∃ s, (updateX86 P).pre s) :
    Verified X86.target (Impl.Blake2.X86.Stream.update w name code) (updateX86 P) :=
  ⟨fun _ hs => Update.correct hP hf (Update.pre_of hs), hct, hsat⟩

theorem finalize_verified (hP : VG.Proof.Blake2.X86.Stream.Ok P) {name : String} {code : Prog isa} (hf : VG.Proof.Blake2.X86.Stream.CalleeOk P code)
    (hct : ConstantTime isa (finalizeX86 P).pre (finalizeX86 P).pub (Impl.Blake2.X86.Stream.finalize w name code))
    (hsat : ∃ s, (finalizeX86 P).pre s) :
    Verified X86.target (Impl.Blake2.X86.Stream.finalize w name code) (finalizeX86 P) :=
  ⟨fun _ hs => Finalize.correct hP hf (Finalize.pre_of hs), hct, hsat⟩

end VG.Proof.Blake2.X86.Stream

end
