module

public import VerifiedGarbage.Proof.X25519.Arm.Verified
public import VerifiedGarbage.Impl.X25519.Arm.Words
public import VerifiedGarbage.Proof.X25519.Arm.Words.Chain
public import VerifiedGarbage.Proof.X25519.Arm.Words.Ladder
import VerifiedGarbage.Proof.X25519.Arm.Words.Mul
import VerifiedGarbage.Proof.X25519.Arm.Words.AddSub
import VerifiedGarbage.Proof.X25519.Arm.Invert
import VerifiedGarbage.Proof.X25519.Field
import VerifiedGarbage.Proof.X25519.Invert
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Arm.Exec
public import VerifiedGarbage.Proof.X25519.Arm.CT
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Proof.X25519.Contract
public import VerifiedGarbage.TCB.Arm.Target

/-!
# X25519 on 32-bit ARM with `umaal`: the whole function

The registers saved and restored (`setup_ok`, `restore_ok`), the u-coordinate
as eight words (`decode_val`, `init_ok`), the result reduced and stored as
bytes (`output_ok`), and `vg_x25519_umaal` (`x25519Umaal_correct`), which meets
the shared contract of `Spec/X25519/Contract.lean` (`x25519Umaal_verified`).
-/

@[expose] public section

namespace VG.Proof.X25519.Arm.Words

open VG VG.Arm VG.Impl.X25519.Arm.Words
open VG.Impl.X25519.Arm (BITS bits)
open VG.Spec.X25519 (P Fe bytesAt)
open VG.Proof.X25519 (leNum leNum_append bytesAt_add length_bytesAt leNum_bytesAt_32bit toFe leBytes toFe_mul
  ladderAfter ladderAfter_swap_le)

/-! ## Saving the registers -/

/-- The registers `g` saved at `[0, 36)` of the working space at `B`. -/
def Saved9 (B : Addr) (g : Reg → BitVec 32) (m : Mem) : Prop :=
  ∀ i < 9, m.readW (B + BitVec.ofNat 64 (4 * i)) 32 = g (savedReg i)

/-- The saved registers stay where no code writes. -/
theorem Saved9.frame {B : Addr} {g : Reg → BitVec 32} {m m' : Mem} (hs : Saved9 B g m) {rs : List Region}
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, ∀ i < 9, Region.Disjoint ⟨B + BitVec.ofNat 64 (4 * i), 4⟩ r) :
    Saved9 B g m' := fun i hi => by
  rw [hf.readW (Region.contains_self _ _) (fun r hr => hd r hr i hi) (by decide)]; exact hs i hi

/-- The saved registers stay under writes above them in the working space. -/
theorem Saved9.above {B : Addr} {g : Reg → BitVec 32} {m m' : Mem} (hs : Saved9 B g m) {e n : Nat}
    (hf : Frame [⟨B + BitVec.ofNat 64 e, n⟩] m m') (he : 36 ≤ e) (hn : e + n ≤ 4096) : Saved9 B g m' :=
  hs.frame hf fun r hr i hi => by
    rw [List.mem_singleton.mp hr]
    exact Offset.disjoint _ (.inl (by omega_using [he, hi])) (by omega_using [hi]) (by omega_using [hn])

section
variable {b : BitVec 32}

theorem saves_ok {s : State} (h3 : s.gpr .r3 = b) (hfit : b.toNat + 4096 ≤ 2 ^ 32)
    (hw : (⟨State.addr b, 4096⟩ : Region) ∈ s.wr) :
    WP isa (.block ((List.range 9).flatMap fun i => ([.str (savedReg i) .r3 (4 * i)] : List Instr))) s fun s' =>
      Saved9 (State.addr b) s.gpr s'.mem ∧ Frame [⟨State.addr b, 36⟩] s.mem s'.mem ∧ s'.gpr = s.gpr ∧
        Rest [] s s' := by
  refine WP.mono (wp_range_flatMap (M := isa)
    (fun n s' => (∀ i < n, s'.mem.readW (State.addr b + BitVec.ofNat 64 (4 * i)) 32 = s.gpr (savedReg i)) ∧
      Frame [⟨State.addr b, 4 * n⟩] s.mem s'.mem ∧ s'.gpr = s.gpr ∧ Rest [] s s')
    (fun n s' hn ⟨h1, h2, h3', h4⟩ => ?_) 9 (Nat.le_refl _) s
    ⟨fun _ h => absurd h (Nat.not_lt_zero _), Frame.refl _ _, rfl, Rest.refl _ _⟩)
    fun s' h => ⟨h.1, h.2.1, h.2.2⟩
  refine wp_str (a := State.addr b + BitVec.ofNat 64 (4 * n)) (by omega_arith)
    (by rw [h3', h3]; exact addr_add (by omega_arith)) (by rw [h4.wr]; exact in_base hw (by omega_arith) (by omega_arith))
    fun s2 u2 => WP.block_nil ⟨fun i hi => ?_, ?_, by rw [u2.gpr, h3'], h4.trans (u2.rest _)⟩
  · rw [u2.mem]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega_arith) (by omega_arith) (by omega_arith)) (by decide)]; exact h1 i hi
    · rw [Mem.readW_writeW_self32, h3']
  · rw [u2.mem]
    exact (h2.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by omega_arith)⟩).writeW
      (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega_arith) (by omega_arith))

theorem setup_ok {s : State} (hp : XPre s) :
    WP isa (.block setup) s fun s' =>
      Ctx (s.gpr .r3) s' ∧ s'.gpr .r12 = s.gpr .r0 ∧ s'.gpr .r1 = s.gpr .r1 ∧ s'.gpr .r2 = s.gpr .r2 ∧
      Saved9 (State.addr (s.gpr .r3)) s.gpr s'.mem ∧ Frame [⟨State.addr (s.gpr .r3), 36⟩] s.mem s'.mem ∧
      Rest [.r0, .r12] s s' := by
  have hw : (⟨State.addr (s.gpr .r3), 4096⟩ : Region) ∈ s.wr := by rw [hp.wr]; simp
  unfold setup
  refine WP.append (saves_ok rfl hp.f3 hw) fun s1 ⟨hsv, hf, hg, hr⟩ => ?_
  refine wp_mov (op2_reg _ _) fun s2 u2 => wp_mov (op2_reg _ _) fun s3 u3 => WP.block_nil ?_
  exact ⟨⟨by rw [u3.gpr, u2.other _ (by decide), hg], hp.f3, by rw [u3.wr, u2.wr, hr.wr]; exact hw⟩,
    by rw [u3.other _ (by decide), u2.gpr, hg], by rw [u3.other _ (by decide), u2.other _ (by decide), hg],
    by rw [u3.other _ (by decide), u2.other _ (by decide), hg], by rw [u3.mem, u2.mem]; exact hsv,
    by rw [u3.mem, u2.mem]; exact hf,
    (hr.mono (by simp)).trans ((u2.rest (by decide)).trans (u3.rest (by decide)))⟩

theorem restore_ok {s : State} (hc : Ctx b s) {g : Reg → BitVec 32} (hs : Saved9 (State.addr b) g s.mem) :
    WP isa (.block restore) s fun s' => (∀ i < 9, s'.gpr (savedReg i) = g (savedReg i)) ∧
      Rest [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .lr] s s' ∧ s'.mem = s.mem := by
  have hsr : ∀ i < 9, savedReg i ∈ [Reg.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .lr] := by decide
  have hinj : ∀ i < 9, ∀ j < 9, savedReg i = savedReg j → i = j := by decide
  refine WP.mono (wp_range_flatMap (M := isa)
    (fun n s' => (∀ i < n, s'.gpr (savedReg i) = g (savedReg i)) ∧
      Rest [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .lr] s s' ∧ s'.mem = s.mem)
    (fun n s' hn ⟨hl, hr, hm⟩ => ?_) 9 (Nat.le_refl _) s
    ⟨fun _ h => absurd h (Nat.not_lt_zero _), Rest.refl _ _, rfl⟩) fun s' h => h
  refine ldr0_ok (hc.of_rest hr (by decide)) (d := 4 * n) (by omega_using [hn]) fun s1 u1 =>
    WP.block_nil ⟨fun i hi => ?_, hr.trans (u1.rest (hsr n hn)), by rw [u1.mem, hm]⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h' | rfl
  · rw [u1.other _ (fun e => absurd (hinj _ (by omega_using [hn, hi]) _ hn e) (by omega_using [h']))]; exact hl i h'
  · rw [u1.gpr, hm, hs i hn]

end

/-! ## The u-coordinate as words -/

/-- Word `k` of the decoded u-coordinate at `p`: the top bit masked. -/
def uWord (m : Mem) (p : Addr) (k : Nat) : Nat :=
  if k = 7 then (m.readW (p + BitVec.ofNat 64 (4 * k)) 32).toNat % 2 ^ 31
  else (m.readW (p + BitVec.ofNat 64 (4 * k)) 32).toNat

theorem leNum_bytesAt4 (m : Mem) (p : Addr) :
    ∀ n, leNum (bytesAt m p (4 * n)) = val32 (fun k => (m.readW (p + BitVec.ofNat 64 (4 * k)) 32).toNat) n
  | 0 => rfl
  | n + 1 => by
    rw [show 4 * (n + 1) = 4 * n + 4 from rfl, bytesAt_add, leNum_append, leNum_bytesAt4 m p n, val32_succ,
      length_bytesAt, leNum_bytesAt_32bit, show (256 : Nat) ^ (4 * n) = 2 ^ (32 * n) by
        rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]; congr 1; omega_arith]

/-- The words of the decoded u-coordinate. -/
theorem decode_val (m : Mem) (p : Addr) :
    val32 (uWord m p) 8 = VG.Spec.X25519.decodeUCoordinate (bytesAt m p 32) := by
  rw [VG.Proof.X25519.decodeUCoordinate_eq (length_bytesAt m p 32), show 32 = 4 * 8 from rfl, leNum_bytesAt4]
  have e : val32 (uWord m p) 7 = val32 (fun k => (m.readW (p + BitVec.ofNat 64 (4 * k)) 32).toNat) 7 :=
    val32_congr fun k hk => by simp only [uWord, show k ≠ 7 by omega_arith, ite_false]
  have hlo : val32 (fun k => (m.readW (p + BitVec.ofNat 64 (4 * k)) 32).toNat) 7 < 2 ^ 224 :=
    val32_lt fun k _ => (m.readW _ 32).isLt
  have h7 := (m.readW (p + BitVec.ofNat 64 (4 * 7)) 32).isLt
  rw [val32_succ (uWord m p) 7, val32_succ _ 7, e]
  simp only [uWord, ite_true]
  omega_arith

theorem byte_of_word (m : Mem) (p : Addr) (d : Nat) {i : Nat} (hi : i < 4) :
    (m (p + BitVec.ofNat 64 (d + i))).toNat = (m.readW (p + BitVec.ofNat 64 d) 32).toNat / 2 ^ (8 * i) % 256 := by
  rw [← Offset.add_add, Mem.readW_byte m _ hi, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]

theorem decodeStep_ok {k : Nat} (hk : k < 8) {s : State} {pt : BitVec 32} (h2 : s.gpr .r2 = pt)
    (hpf : pt.toNat + 32 ≤ 2 ^ 32) (hin : (⟨State.addr pt, 32⟩ : Region) ∈ s.rd ++ s.wr) :
    WP isa (.block (decodeStep k)) s fun s' =>
      (s'.gpr (xr k)).toNat = uWord s.mem (State.addr pt) k ∧ UKeep (xr k) [.r3] s s' := by
  have hx := xr_ne k
  have ld : ∀ {t : Reg} {i : Nat} {s' : State} {is : List Instr} {Q : State → Prop}, i < 32 → s'.gpr .r2 = pt →
      s'.rd = s.rd → s'.wr = s.wr →
      (∀ s'', Upd s' s'' t ((s'.mem (State.addr pt + BitVec.ofNat 64 i)).setWidth 32) → WP isa (.block is) s'' Q) →
      WP isa (.block (.ldrb t .r2 i :: is)) s' Q := fun hi h2' hrd hwr k' =>
    wp_ldrb (by omega_using [hi]) (by rw [h2']; exact addr_add (by omega_using [hi, hpf]))
      (by rw [hrd, hwr]; exact in_base hin (by omega_using [hi]) (by omega_using [hi])) k'
  have hw := (s.mem.readW (State.addr pt + BitVec.ofNat 64 (4 * k)) 32).isLt
  unfold decodeStep
  simp only [List.cons_append, List.nil_append]
  refine ld (by omega_using [hk]) h2 rfl rfl fun s1 u1 => ?_
  refine ld (by omega_using [hk]) (by rw [u1.other _ hx.2.2.1, h2]) u1.rd u1.wr fun s2 u2 => ?_
  refine wp_dp (op2_lsl (by decide)) fun s3 u3 => ?_
  refine ld (by omega_using [hk]) (by rw [u3.other _ hx.2.2.1, u2.other _ (by decide), u1.other _ hx.2.2.1, h2])
    (by rw [u3.rd, u2.rd, u1.rd]) (by rw [u3.wr, u2.wr, u1.wr]) fun s4 u4 => ?_
  refine wp_dp (op2_lsl (by decide)) fun s5 u5 => ?_
  refine ld (by omega_using [hk])
    (by rw [u5.other _ hx.2.2.1, u4.other _ (by decide), u3.other _ hx.2.2.1, u2.other _ (by decide),
      u1.other _ hx.2.2.1, h2])
    (by rw [u5.rd, u4.rd, u3.rd, u2.rd, u1.rd]) (by rw [u5.wr, u4.wr, u3.wr, u2.wr, u1.wr]) fun s6 u6 => ?_
  -- The bytes, as parts of the word.
  have b0 : (s1.gpr (xr k)).toNat = (s.mem.readW (State.addr pt + BitVec.ofNat 64 (4 * k)) 32).toNat % 256 := by
    rw [u1.gpr, toNat_setWidth8]
    have := byte_of_word s.mem (State.addr pt) (4 * k) (i := 0) (by decide)
    simpa using this
  have b1 : (s2.gpr .r3).toNat = (s.mem.readW (State.addr pt + BitVec.ofNat 64 (4 * k)) 32).toNat / 256 % 256 := by
    rw [u2.gpr, u1.mem, toNat_setWidth8]
    exact byte_of_word s.mem (State.addr pt) (4 * k) (i := 1) (by decide)
  have e3 : (s3.gpr (xr k)).toNat = (s.mem.readW (State.addr pt + BitVec.ofNat 64 (4 * k)) 32).toNat % 65536 := by
    rw [u3.gpr]
    show (s2.gpr (xr k) + s2.gpr .r3 <<< 8).toNat = _
    rw [BitVec.toNat_add, toNat_shl, u2.other _ hx.2.2.2.1.symm, b0, b1]
    omega_arith
  have b2 : (s4.gpr .r3).toNat = (s.mem.readW (State.addr pt + BitVec.ofNat 64 (4 * k)) 32).toNat / 65536 % 256 := by
    rw [u4.gpr, u3.mem, u2.mem, u1.mem, toNat_setWidth8]
    exact byte_of_word s.mem (State.addr pt) (4 * k) (i := 2) (by decide)
  have e5 : (s5.gpr (xr k)).toNat = (s.mem.readW (State.addr pt + BitVec.ofNat 64 (4 * k)) 32).toNat % 16777216 := by
    rw [u5.gpr]
    show (s4.gpr (xr k) + s4.gpr .r3 <<< 16).toNat = _
    rw [BitVec.toNat_add, toNat_shl, u4.other _ hx.2.2.2.1.symm, e3, b2]
    omega_arith
  have b3 : (s6.gpr .r3).toNat = (s.mem.readW (State.addr pt + BitVec.ofNat 64 (4 * k)) 32).toNat / 16777216 % 256 := by
    rw [u6.gpr, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem, toNat_setWidth8]
    exact byte_of_word s.mem (State.addr pt) (4 * k) (i := 3) (by decide)
  have k6 : UKeep (xr k) [.r3] s s6 := ⟨fun r hT hX => by
      have h3 : r ≠ .r3 := fun e => hT (e ▸ List.mem_singleton_self _)
      rw [u6.other r h3, u5.other r hX, u4.other r h3, u3.other r hX, u2.other r h3, u1.other r hX],
    by rw [u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem], by rw [u6.rd, u5.rd, u4.rd, u3.rd, u2.rd, u1.rd],
    by rw [u6.wr, u5.wr, u4.wr, u3.wr, u2.wr, u1.wr], by rw [u6.sp, u5.sp, u4.sp, u3.sp, u2.sp, u1.sp]⟩
  have key : ∀ s7 : State,
      (s7.gpr (xr k)).toNat = (s.mem.readW (State.addr pt + BitVec.ofNat 64 (4 * k)) 32).toNat % 16777216 →
      (s7.gpr .r3).toNat = (if k = 7
        then (s.mem.readW (State.addr pt + BitVec.ofNat 64 (4 * k)) 32).toNat / 16777216 % 128
        else (s.mem.readW (State.addr pt + BitVec.ofNat 64 (4 * k)) 32).toNat / 16777216 % 256) →
      UKeep (xr k) [.r3] s s7 →
      WP isa (.block [.dp .add (xr k) (xr k) (.shifted .r3 .lsl 24)]) s7 fun s' =>
        (s'.gpr (xr k)).toNat = uWord s.mem (State.addr pt) k ∧ UKeep (xr k) [.r3] s s' := by
    intro s7 e4 e5' k7
    refine wp_dp (op2_lsl (by decide)) fun s8 u8 => WP.block_nil ⟨?_, ?_⟩
    · rw [u8.gpr]
      show (s7.gpr (xr k) + s7.gpr .r3 <<< 24).toNat = _
      rw [BitVec.toNat_add, toNat_shl, e4, e5', uWord]
      split <;> omega_arith
    · exact ⟨fun r hT hX => by rw [u8.other r hX, k7.keep r hT hX], by rw [u8.mem, k7.mem], by rw [u8.rd, k7.rd],
        by rw [u8.wr, k7.wr], by rw [u8.sp, k7.sp]⟩
  by_cases h7 : k = 7
  · simp only [h7, ite_true, List.cons_append, List.nil_append] at key ⊢
    subst h7
    refine wp_dp (op2_imm (by decide)) fun s7 u7 =>
      key s7 (by rw [u7.other _ hx.2.2.2.1.symm, u6.other _ hx.2.2.2.1.symm, e5]) ?_
      ⟨fun r hT hX => by
        rw [u7.other r fun e => hT (e ▸ List.mem_singleton_self _), k6.keep r hT hX], by rw [u7.mem, k6.mem],
        by rw [u7.rd, k6.rd], by rw [u7.wr, k6.wr], by rw [u7.sp, k6.sp]⟩
    rw [u7.gpr]
    show (s6.gpr .r3 &&& 127).toNat = _
    rw [BitVec.toNat_and, b3, show (127 : BitVec 32).toNat = 2 ^ 7 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
    omega_arith
  · simp only [h7, ite_false, List.nil_append] at key ⊢
    exact key s6 (by rw [u6.other _ hx.2.2.2.1.symm, e5]) b3 k6

theorem decode_ok {s0 : State} {pt : BitVec 32} (h2 : s0.gpr .r2 = pt) (hpf : pt.toNat + 32 ≤ 2 ^ 32)
    (hin : (⟨State.addr pt, 32⟩ : Region) ∈ s0.rd ++ s0.wr) :
    WP isa (.block ((List.range 8).flatMap decodeStep)) s0 fun s' =>
      (∀ k < 8, (s'.gpr (xr k)).toNat = uWord s0.mem (State.addr pt) k) ∧
      (∀ r, r ∉ [Reg.r3] → (∀ j < 8, r ≠ xr j) → s'.gpr r = s0.gpr r) ∧
      s'.mem = s0.mem ∧ s'.rd = s0.rd ∧ s'.wr = s0.wr ∧ s'.sp = s0.sp := by
  refine wp_range_flatMap (M := isa)
    (fun n s => (∀ k < n, (s.gpr (xr k)).toNat = uWord s0.mem (State.addr pt) k) ∧
      (∀ r, r ∉ [Reg.r3] → (∀ j < n, r ≠ xr j) → s.gpr r = s0.gpr r) ∧
      s.mem = s0.mem ∧ s.rd = s0.rd ∧ s.wr = s0.wr ∧ s.sp = s0.sp)
    (fun n s hn ⟨hv, hk, hm, hrd, hwr, hsp⟩ => ?_) 8 (Nat.le_refl _) s0
    ⟨fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ _ => rfl, rfl, rfl, rfl, rfl⟩
  refine WP.mono (decodeStep_ok hn (pt := pt) (by rw [hk _ (by decide) fun j _ => (xr_ne j).2.2.1, h2]) hpf
    (by rw [hrd, hwr]; exact hin)) fun s' ⟨hv', hk'⟩ => ⟨fun j hj => ?_, fun r hT hX => ?_, by rw [hk'.mem, hm],
      by rw [hk'.rd, hrd], by rw [hk'.wr, hwr], by rw [hk'.sp, hsp]⟩
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [hk'.keep _ (fun hm' => (xr_ne j).2.2.2.1 (List.mem_singleton.mp hm').symm) (xr_inj' hn hj).symm]
      exact hv j hj
    · rw [hv', hm]
  · rw [hk'.keep r hT (hX n (Nat.lt_succ_self n)), hk r hT fun j hj => hX j (Nat.lt_succ_of_lt hj)]

/-! ## The initial elements -/

section
variable {b : BitVec 32}

/-- The registers `X` stored as the element at `o`, and what stays. -/
theorem storeSlot_ok {X : Nat → Reg} {o : Nat} (ho : o + 32 ≤ 4096) {s : State} (hc : Ctx b s) :
    WP isa (.block (stores o X)) s fun s' =>
      W s'.mem (State.addr b) o = val32 (fun k => (s.gpr (X k)).toNat) 8 ∧
      (∀ d, d + 4 ≤ o ∨ o + 32 ≤ d → d + 4 ≤ 4096 → wd s'.mem (State.addr b) d = wd s.mem (State.addr b) d) ∧
      Frame [⟨State.addr b + BitVec.ofNat 64 o, 32⟩] s.mem s'.mem ∧ s'.gpr = s.gpr ∧ Kp s s' :=
  WP.mono (stores_ok ho hc) fun s' ⟨hw, hf, hg, hr⟩ => ⟨W_of hw, fun d hd hb => wd_frame hf fun r hr' => by
    rw [List.mem_singleton.mp hr']; exact Offset.disjoint _ hd (by omega_using [hb]) (by omega_using [ho]),
    hf, hg, Kp.of_rest hr List.not_mem_nil⟩

theorem W_keep {m m' : Mem} {B : Addr} {o q : Nat}
    (h : ∀ d, d + 4 ≤ o ∨ o + 32 ≤ d → d + 4 ≤ 4096 → wd m' B d = wd m B d) (hq : q + 32 ≤ o ∨ o + 32 ≤ q)
    (hb : q + 32 ≤ 4096) : W m' B q = W m B q :=
  val32_congr fun k hk => h _ (by omega_using [hq, hk]) (by omega_using [hb, hk])

theorem ones_ok {s : State} :
    WP isa (.block ((List.range 8).flatMap fun k =>
      ([.mov (xr k) (.imm (if k = 0 then 1 else 0))] : List Instr))) s fun s' =>
      (∀ k < 8, (s'.gpr (xr k)).toNat = if k = 0 then 1 else 0) ∧ Kp s s' ∧ s'.mem = s.mem := by
  refine wp_range_flatMap (M := isa)
    (fun m s' => (∀ k < m, (s'.gpr (xr k)).toNat = if k = 0 then 1 else 0) ∧ Kp s s' ∧ s'.mem = s.mem)
    (fun m s' hm ⟨h1, h2, h3⟩ => ?_) 8 (Nat.le_refl _) s
    ⟨fun _ h => absurd h (Nat.not_lt_zero _), Kp.refl _, rfl⟩
  refine wp_mov (op2_imm (by split <;> decide)) fun s2 u2 => WP.block_nil
    ⟨fun j hj => ?_, h2.trans (Kp.of_upd u2 (xr_ne m).1), by rw [u2.mem, h3]⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
  · rw [u2.other _ (xr_inj' hm hj).symm]; exact h1 j hj
  · rw [u2.gpr]; split <;> rfl

theorem init_ok {s : State} (hc : Ctx b s) {o pt : BitVec 32} (h12 : s.gpr .r12 = o) (h2 : s.gpr .r2 = pt)
    (hpf : pt.toNat + 32 ≤ 2 ^ 32) (hin : (⟨State.addr pt, 32⟩ : Region) ∈ s.rd ++ s.wr)
    (hd : Region.Disjoint ⟨State.addr pt, 32⟩ ⟨State.addr b, 4096⟩) :
    WP isa (.block Impl.X25519.Arm.Words.init) s fun s' =>
      Kp s s' ∧ Frame [⟨State.addr b + BitVec.ofNat 64 40, 184⟩] s.mem s'.mem ∧
      s'.mem.readW (State.addr b + BitVec.ofNat 64 OUT) 32 = o ∧
      SlotsW s'.mem (State.addr b) LQ LQ
        (ladV (toFe (VG.Spec.X25519.decodeUCoordinate (bytesAt s.mem (State.addr pt) 32)))
          (VG.Proof.X25519.init (toFe (VG.Spec.X25519.decodeUCoordinate (bytesAt s.mem (State.addr pt) 32))))) := by
  have hP : P = 2 ^ 255 - 19 := rfl
  have hO : OUT = 40 := rfl
  unfold Impl.X25519.Arm.Words.init
  simp only [List.append_assoc]
  refine str0_ok hc (d := OUT) (by decide) fun s1 u1 => ?_
  have k1 : Kp s s1 := Kp.of_mupd u1
  have hf1 : Frame [⟨State.addr b + BitVec.ofNat 64 40, 184⟩] s.mem s1.mem := by
    rw [u1.mem]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains _ (d := OUT) (n := 4) (by decide) (by decide) (by decide))
  -- The u-coordinate is as it was.
  have hu : bytesAt s1.mem (State.addr pt) 32 = bytesAt s.mem (State.addr pt) 32 :=
    bytesAt_frame hf1 fun r hr => by
      rw [List.mem_singleton.mp hr]; exact hd.sub_right (Offset.sub_base _ (by decide))
  refine WP.append (decode_ok (s0 := s1) (pt := pt) (by rw [u1.gpr, h2]) hpf (by rw [u1.rd, u1.wr]; exact hin))
    fun s2 ⟨hv2, hk2, hm2, hrd2, hwr2, hsp2⟩ => ?_
  have k2 : Kp s s2 := k1.trans ⟨hk2 _ (by decide) fun j _ => (xr_ne j).1, hrd2, hwr2, hsp2⟩
  refine WP.append (storeSlot_ok (X := xr) (o := X1) (by decide) (k2.ctx hc)) fun s3 ⟨hW3, hk3, hf3, hg3, kp3⟩ => ?_
  have k3 := k2.trans kp3
  refine WP.append (storeSlot_ok (X := xr) (o := X3) (by decide) (k3.ctx hc)) fun s4 ⟨hW4, hk4, hf4, hg4, kp4⟩ => ?_
  have k4 := k3.trans kp4
  refine WP.append ones_ok fun s5 ⟨hv5, kp5, hm5⟩ => ?_
  have k5 := k4.trans kp5
  refine WP.append (storeSlot_ok (X := xr) (o := X2) (by decide) (k5.ctx hc)) fun s6 ⟨hW6, hk6, hf6, hg6, kp6⟩ => ?_
  have k6 := k5.trans kp6
  refine WP.append (storeSlot_ok (X := xr) (o := Z3) (by decide) (k6.ctx hc)) fun s7 ⟨hW7, hk7, hf7, hg7, kp7⟩ => ?_
  have k7 := k6.trans kp7
  refine wp_mov (op2_imm (by decide)) fun s8 u8 => ?_
  have k8 := k7.trans (Kp.of_upd u8 (xr_ne 0).1)
  refine WP.mono (storeSlot_ok (X := xr) (o := Z2) (by decide) (k8.ctx hc)) fun s9 ⟨hW9, hk9, hf9, hg9, kp9⟩ => ?_
  -- The values.
  have eU : val32 (fun k => (s2.gpr (xr k)).toNat) 8 =
      VG.Spec.X25519.decodeUCoordinate (bytesAt s.mem (State.addr pt) 32) := by
    rw [val32_congr hv2, decode_val, hu]
  have hUlt : VG.Spec.X25519.decodeUCoordinate (bytesAt s.mem (State.addr pt) 32) < 2 ^ 255 := by
    rw [VG.Proof.X25519.decodeUCoordinate_eq (length_bytesAt _ _ 32)]; exact Nat.mod_lt _ (by decide)
  have e1 : val32 (fun k => (s5.gpr (xr k)).toNat) 8 = 1 := by rw [val32_congr hv5]; exact val32_one
  have e0 : val32 (fun k => (s8.gpr (xr k)).toNat) 8 = 0 := by
    rw [val32_congr (g := fun _ => 0) fun k hk => by
      show (s8.gpr (xr k)).toNat = 0
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · rw [u8.gpr]; rfl
      · rw [u8.other _ (xr_inj' hk hk0), hg7, hg6, hv5 k hk]
        simp only [show k ≠ 0 by omega_using [hk0], ite_false], val32_zero_fn]
  have wX1 : W s9.mem (State.addr b) X1 = VG.Spec.X25519.decodeUCoordinate (bytesAt s.mem (State.addr pt) 32) := by
    rw [W_keep hk9 (by decide) (by decide), u8.mem, W_keep hk7 (by decide) (by decide),
      W_keep hk6 (by decide) (by decide), hm5, W_keep hk4 (by decide) (by decide), hW3, eU]
  have wX3 : W s9.mem (State.addr b) X3 = VG.Spec.X25519.decodeUCoordinate (bytesAt s.mem (State.addr pt) 32) := by
    rw [W_keep hk9 (by decide) (by decide), u8.mem, W_keep hk7 (by decide) (by decide),
      W_keep hk6 (by decide) (by decide), hm5, hW4, hg3, eU]
  have wX2 : W s9.mem (State.addr b) X2 = 1 := by
    rw [W_keep hk9 (by decide) (by decide), u8.mem, W_keep hk7 (by decide) (by decide), hW6, e1]
  have wZ3 : W s9.mem (State.addr b) Z3 = 1 := by
    rw [W_keep hk9 (by decide) (by decide), u8.mem, hW7, hg6, e1]
  have wZ2 : W s9.mem (State.addr b) Z2 = 0 := by rw [hW9, e0]
  refine ⟨k8.trans kp9, ?_, ?_, fun q hq => ?_⟩
  · have fr : ∀ {m m' : Mem} {z : Nat}, Frame [⟨State.addr b + BitVec.ofNat 64 z, 32⟩] m m' → 40 ≤ z →
        z + 32 ≤ 224 → Frame [⟨State.addr b + BitVec.ofNat 64 40, 184⟩] m m' := fun hf h1 h2 =>
      hf.sub fun r hr => ⟨_, List.mem_singleton_self _, by
        rw [List.mem_singleton.mp hr]; exact Offset.sub _ h1 (by omega_using [h2])⟩
    refine hf1.trans ?_
    rw [← hm2]
    refine (fr hf3 (by decide) (by decide)).trans ((fr hf4 (by decide) (by decide)).trans ?_)
    rw [← hm5]
    refine (fr hf6 (by decide) (by decide)).trans ((fr hf7 (by decide) (by decide)).trans ?_)
    rw [← u8.mem]
    exact fr hf9 (by decide) (by decide)
  · apply BitVec.eq_of_toNat_eq
    have : wd s9.mem (State.addr b) OUT = wd s1.mem (State.addr b) OUT := by
      rw [hk9 _ (by decide) (by decide), u8.mem, hk7 _ (by decide) (by decide), hk6 _ (by decide) (by decide), hm5,
        hk4 _ (by decide) (by decide), hk3 _ (by decide) (by decide), hm2]
    rw [show (s9.mem.readW (State.addr b + BitVec.ofNat 64 OUT) 32).toNat = wd s9.mem (State.addr b) OUT from rfl,
      this, u1.mem, wd_write_self, h12]
  · simp only [LQ, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact ⟨by decide, by rw [wX1]; rfl, fun _ => by rw [wX1]; omega_using [hUlt, hP]⟩
    · exact ⟨by decide, by rw [wX2]; rfl, fun _ => by rw [wX2]; omega_using [hP]⟩
    · exact ⟨by decide, by rw [wZ2]; rfl, fun _ => by rw [wZ2]; omega_using [hP]⟩
    · exact ⟨by decide, by rw [wX3]; rfl, fun _ => by rw [wX3]; omega_using [hUlt, hP]⟩
    · exact ⟨by decide, by rw [wZ3]; rfl, fun _ => by rw [wZ3]; omega_using [hP]⟩

/-! ## The last swap -/

theorem lastSwap_ok {s : State} (hc : Ctx b s) {sw : Nat} (hsw : sw ≤ 1)
    (hs : wd s.mem (State.addr b) SWAP = sw) {v : Nat → Fe} (hS : SlotsW s.mem (State.addr b) LQ LQ v) :
    WP isa (.block lastSwap) s fun s' => Kp s s' ∧ Frame [FAW b] s.mem s'.mem ∧
      SlotsW s'.mem (State.addr b) LQ LQ (swapV Z2 Z3 sw (swapV X2 X3 sw v)) := by
  unfold lastSwap
  simp only [List.cons_append, List.nil_append]
  refine ldr0_ok hc (d := SWAP) (by decide) fun s1 u1 => wp_mov (op2_imm (by decide)) fun s2 u2 =>
    wp_dp (op2_reg _ _) fun s3 u3 => ?_
  have e9 : s3.gpr .r9 = 0 - BitVec.ofNat 32 sw := by
    rw [u3.gpr]
    show s2.gpr .r9 - s2.gpr .r2 = _
    rw [u2.gpr, u2.other _ (by decide), u1.gpr]
    congr 1
    apply BitVec.eq_of_toNat_eq
    rw [toNat_imm (by omega_using [hsw])]; exact hs
  have k3 : Kp s s3 := (Kp.of_upd u1 (by decide)).trans ((Kp.of_upd u2 (by decide)).trans (Kp.of_upd u3 (by decide)))
  have hm3 : s3.mem = s.mem := by rw [u3.mem, u2.mem, u1.mem]
  have h3 : Cur b s3 (wd s3.mem (State.addr b) CNT) sw LQ LQ v s3 :=
    ⟨k3.ctx hc, Kp.refl _, Frame.refl _ _, rfl, by rw [hm3]; exact hs, by rw [hm3]; exact hS⟩
  refine WP.append (opCswap (x := X2) (y := X3) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) h3 hsw e9) fun s4 ⟨h4, h9'⟩ => ?_
  exact WP.mono (opCswap (x := Z2) (y := Z3) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) h4 hsw (by rw [h9', e9])) fun s5 h5 =>
    ⟨k3.trans h5.1.kp, by rw [← hm3]; exact h5.1.frame, h5.1.slots⟩

/-! ## The output -/

/-- The element at `o` into the registers `xr`. -/
theorem loads_ok {o : Nat} (ho : o + 32 ≤ 4096) {s : State} (hc : Ctx b s) :
    WP isa (.block ((List.range 8).flatMap fun k => ([.ldr (xr k) .r0 (o + 4 * k)] : List Instr))) s fun s' =>
      (∀ k < 8, (s'.gpr (xr k)).toNat = wd s.mem (State.addr b) (o + 4 * k)) ∧
      (∀ r, (∀ j < 8, r ≠ xr j) → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  refine wp_range_flatMap (M := isa)
    (fun n s' => (∀ k < n, (s'.gpr (xr k)).toNat = wd s.mem (State.addr b) (o + 4 * k)) ∧
      (∀ r, (∀ j < n, r ≠ xr j) → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp)
    (fun n s' hn ⟨hv, hk, hm, hrd, hwr, hsp⟩ => ?_) 8 (Nat.le_refl _) s
    ⟨fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
  have hc' : Ctx b s' := (⟨hk _ fun j _ => (xr_ne j).1, hrd, hwr, hsp⟩ : Kp s s').ctx hc
  refine ldr0_ok hc' (d := o + 4 * n) (by omega_using [ho, hn]) fun s1 u1 => WP.block_nil
    ⟨fun j hj => ?_, fun r hX => by rw [u1.other r (hX n (Nat.lt_succ_self n)), hk r fun j hj => hX j (Nat.lt_succ_of_lt hj)],
      by rw [u1.mem, hm], by rw [u1.rd, hrd], by rw [u1.wr, hwr], by rw [u1.sp, hsp]⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
  · rw [u1.other _ (xr_inj' hn hj).symm]; exact hv j hj
  · rw [u1.gpr, hm]; rfl

/-- The words of a number of eight words. -/
theorem val32_div {f : Nat → Nat} {n : Nat} (hf : ∀ k < n, f k < 2 ^ 32) {k : Nat} (hk : k < n) :
    val32 f n / 2 ^ (32 * k) % 2 ^ 32 = f k := by
  have e := val32_append f k (n - k)
  rw [Nat.add_sub_cancel' (by omega_arith)] at e
  have e' := val32_append (fun j => f (k + j)) 1 (n - k - 1)
  rw [Nat.add_sub_cancel' (by omega_arith)] at e'
  simp only [val32, Nat.mul_zero, Nat.pow_zero, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.mul_one] at e'
  have hlt := val32_lt (f := f) (n := k) fun j hj => hf j (by omega_arith)
  rw [e, e', Nat.mul_comm (2 ^ (32 * k)), Nat.add_mul_div_right _ _ (Nat.two_pow_pos _),
    Nat.div_eq_of_lt hlt, Nat.zero_add, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hf k hk)]

/-- Byte `e` of the number of the words `f`. -/
def outB (f : Nat → Nat) (e : Nat) : Byte := BitVec.ofNat 8 (f (e / 4) / 2 ^ (8 * (e % 4)))

theorem outB_at (f : Nat → Nat) (k : Nat) {r : Nat} (hr : r < 4) :
    outB f (4 * k + r) = BitVec.ofNat 8 (f k / 2 ^ (8 * r)) := by
  unfold outB
  rw [show (4 * k + r) / 4 = k by omega_using [hr], show (4 * k + r) % 4 = r by omega_using [hr]]

theorem bytesAt_out {m : Mem} {O : Addr} {f : Nat → Nat} (hf : ∀ k < 8, f k < 2 ^ 32)
    (h : ∀ e < 32, m (O + BitVec.ofNat 64 e) = outB f e) : bytesAt m O 32 = leBytes 32 (val32 f 8) := by
  simp only [bytesAt, leBytes]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  obtain ⟨k, r, hr, rfl⟩ : ∃ k r, r < 4 ∧ i = 4 * k + r :=
    ⟨i / 4, i % 4, Nat.mod_lt _ (by decide), by omega_arith⟩
  have hk : k < 8 := by omega_using [hi]
  rw [h _ hi, outB_at f k hr]
  refine ofNat8_eq ?_
  have hd := val32_div hf hk
  rw [Nat.pow_add, show (256 : Nat) ^ (4 * k) = 2 ^ (32 * k) by
    rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]; congr 1; omega_arith, ← Nat.div_div_eq_div_mul, ← hd]
  generalize val32 f 8 / 2 ^ (32 * k) = y
  have hr' : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega_using [hr]
  rcases hr' with rfl | rfl | rfl | rfl <;> simp only [Nat.reduceMul, Nat.reducePow] <;> omega_arith

/-- While storing the result at `O`, from `s0`, after `n` bytes. -/
structure OutInv (O : Addr) (f : Nat → Nat) (s0 : State) (n : Nat) (s : State) : Prop where
  frame : Frame [⟨O, n⟩] s0.mem s.mem
  bytes : ∀ e < n, s.mem (O + BitVec.ofNat 64 e) = outB f e

theorem OutInv.of_mem {O : Addr} {f : Nat → Nat} {s0 s s' : State} {n : Nat} (h : OutInv O f s0 n s)
    (hm : s'.mem = s.mem) : OutInv O f s0 n s' := ⟨by rw [hm]; exact h.frame, by rw [hm]; exact h.bytes⟩

theorem strb_ok {t : Reg} {n : Nat} (hn : n < 32) {s0 s : State} {o : BitVec 32} (h1 : s.gpr .r1 = o)
    (hofit : o.toNat + 32 ≤ 2 ^ 32) (hout : (⟨State.addr o, 32⟩ : Region) ∈ s.wr) {f : Nat → Nat}
    (h : OutInv (State.addr o) f s0 n s) (hv : (s.gpr t).setWidth 8 = outB f n) {is : List Instr}
    {Q : State → Prop}
    (k : ∀ s', Mupd s s' s'.mem → OutInv (State.addr o) f s0 (n + 1) s' → WP isa (.block is) s' Q) :
    WP isa (.block (.strb t .r1 n :: is)) s Q := by
  refine wp_strb (a := State.addr o + BitVec.ofNat 64 n) (by omega_using [hn])
    (by rw [h1]; exact addr_add (by omega_using [hofit, hn]))
    (in_base hout (by omega_using [hn]) (by omega_using [hn])) fun s1 u1 =>
    k s1 ⟨u1.gpr, rfl, u1.rd, u1.wr, u1.sp⟩ ⟨?_, fun e he => ?_⟩
  · rw [u1.mem]
    exact (h.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by omega_using [])⟩).writeW
      (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega_using []) (by omega_using [hn]))
  · rw [u1.mem, VG.WriteBytes.writeW8_apply]
    rcases Nat.lt_succ_iff_lt_or_eq.mp he with he | rfl
    · rw [iteF (Offset.add_ofNat_ne _ (by omega_using [he, hn]) (by omega_using [hn]) (by omega_using [he]))]
      exact h.bytes e he
    · rw [iteT rfl]; exact hv

theorem out_ok {s0 : State} {o : BitVec 32} (h1 : s0.gpr .r1 = o) (hofit : o.toNat + 32 ≤ 2 ^ 32)
    (hout : (⟨State.addr o, 32⟩ : Region) ∈ s0.wr) :
    WP isa (.block ((List.range 8).flatMap outStep)) s0 fun s' =>
      OutInv (State.addr o) (fun k => (s0.gpr (xr k)).toNat) s0 32 s' ∧ Rest [.r2] s0 s' := by
  refine wp_range_flatMap (M := isa)
    (fun n s => OutInv (State.addr o) (fun k => (s0.gpr (xr k)).toNat) s0 (4 * n) s ∧ Rest [.r2] s0 s)
    (fun k s hk ⟨hi, hr⟩ => ?_) 8 (Nat.le_refl _) s0
    ⟨⟨Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩, Rest.refl _ _⟩
  have hx := xr_ne k
  have ev : (s.gpr (xr k)).toNat = (s0.gpr (xr k)).toNat := by
    rw [hr.gpr _ fun h => hx.2.2.1 (List.mem_singleton.mp h).symm]
  unfold outStep
  refine strb_ok (s0 := s0) (n := 4 * k) (by omega_using [hk]) (by rw [hr.gpr _ (by decide), h1]) hofit
    (by rw [hr.wr]; exact hout) hi
    (by rw [show outB (fun k => (s0.gpr (xr k)).toNat) (4 * k) = _ from outB_at _ k (r := 0) (by decide)]
        exact byte_eq (by rw [ev]; simp)) fun t1 v1 i1 => ?_
  refine wp_mov (op2_lsr (by decide)) fun t2 v2 => ?_
  refine strb_ok (s0 := s0) (n := 4 * k + 1) (by omega_using [hk])
    (by rw [v2.other _ (by decide), v1.gpr, hr.gpr _ (by decide), h1]) hofit
    (by rw [v2.wr, v1.wr, hr.wr]; exact hout) (i1.of_mem v2.mem)
    (by rw [outB_at _ k (r := 1) (by decide)]
        exact byte_eq (by rw [v2.gpr, toNat_shr, v1.gpr, ev])) fun t3 v3 i3 => ?_
  refine wp_mov (op2_lsr (by decide)) fun t4 v4 => ?_
  refine strb_ok (s0 := s0) (n := 4 * k + 2) (by omega_using [hk])
    (by rw [v4.other _ (by decide), v3.gpr, v2.other _ (by decide), v1.gpr, hr.gpr _ (by decide), h1]) hofit
    (by rw [v4.wr, v3.wr, v2.wr, v1.wr, hr.wr]; exact hout)
    (i3.of_mem v4.mem)
    (by rw [outB_at _ k (r := 2) (by decide)]
        exact byte_eq (by rw [v4.gpr, toNat_shr, v3.gpr, v2.other _ hx.2.2.1.symm, v1.gpr, ev])) fun t5 v5 i5 => ?_
  refine wp_mov (op2_lsr (by decide)) fun t6 v6 => ?_
  refine strb_ok (s0 := s0) (n := 4 * k + 3) (by omega_using [hk])
    (by rw [v6.other _ (by decide), v5.gpr, v4.other _ (by decide), v3.gpr, v2.other _ (by decide), v1.gpr,
      hr.gpr _ (by decide), h1]) hofit
    (by rw [v6.wr, v5.wr, v4.wr, v3.wr, v2.wr, v1.wr, hr.wr]; exact hout)
    (i5.of_mem v6.mem)
    (by rw [outB_at _ k (r := 3) (by decide)]
        exact byte_eq (by
          rw [v6.gpr, toNat_shr, v5.gpr, v4.other _ hx.2.2.1.symm, v3.gpr, v2.other _ hx.2.2.1.symm, v1.gpr, ev]))
    fun t7 v7 i7 => WP.block_nil ⟨i7, ?_⟩
  exact hr.trans ((v1.rest _).trans ((v2.rest (by decide)).trans ((v3.rest _).trans ((v4.rest (by decide)).trans
    ((v5.rest _).trans ((v6.rest (by decide)).trans (v7.rest _)))))))

/-- `[X2]`, below `2p`, reduced fully, into `out`. -/
theorem output_ok {s : State} (hc : Ctx b s) (hl : W s.mem (State.addr b) X2 < 2 * P) {o : BitVec 32}
    (ho : s.mem.readW (State.addr b + BitVec.ofNat 64 OUT) 32 = o) (hout : (⟨State.addr o, 32⟩ : Region) ∈ s.wr)
    (hofit : o.toNat + 32 ≤ 2 ^ 32) :
    WP isa (.block output) s fun s' =>
      bytesAt s'.mem (State.addr o) 32 = leBytes 32 (W s.mem (State.addr b) X2 % P) ∧ Kp s s' ∧
      Frame [⟨State.addr o, 32⟩] s.mem s'.mem := by
  unfold output
  simp only [List.cons_append, List.nil_append, List.append_assoc]
  refine WP.append (loads_ok (o := X2) (by decide) hc) fun s1 ⟨hv1, hk1, hm1, hrd1, hwr1, hsp1⟩ => ?_
  have k1 : Kp s s1 := ⟨hk1 _ fun j _ => (xr_ne j).1, hrd1, hwr1, hsp1⟩
  have e1 : val32 (fun k => (s1.gpr (xr k)).toNat) 8 = W s.mem (State.addr b) X2 := val32_congr hv1
  refine WP.append (freeze_ok (s := s1) (by rw [e1]; exact hl)) fun s2 ⟨hv2, hk2, hm2, hrd2, hwr2, hsp2⟩ => ?_
  have k2 : Kp s1 s2 := ⟨hk2 _ (by decide) fun j _ => (xr_ne j).1, hrd2, hwr2, hsp2⟩
  refine ldr0_ok (k2.ctx (k1.ctx hc)) (d := OUT) (by decide) fun s3 u3 => ?_
  have k3 : Kp s s3 := k1.trans (k2.trans (Kp.of_upd u3 (by decide)))
  have hm3 : s3.mem = s.mem := by rw [u3.mem, hm2, hm1]
  refine WP.mono (out_ok (s0 := s3) (o := o) (by rw [u3.gpr, hm2, hm1, ho]) hofit (by rw [k3.wr]; exact hout))
    fun s4 ⟨hi, hr⟩ => ⟨?_, k3.trans (Kp.of_rest hr (by decide)), by rw [← hm3]; exact hi.frame⟩
  rw [bytesAt_out (fun k _ => (s3.gpr (xr k)).isLt) hi.bytes, ← e1, ← hv2]
  exact congrArg _ (val32_congr fun k _ => by
    show (s3.gpr (xr k)).toNat = (s2.gpr (xr k)).toNat
    rw [u3.other _ (xr_ne k).2.1.symm])

end

/-! ## The whole function -/

/-- `vg_x25519_umaal` writes `X25519(k, u)` to `out`, restoring the registers. -/
theorem x25519Umaal_correct {s : State} (hp : XPre s) :
    WP isa x25519Umaal s fun s' => abiPreserved s s' ∧ x25519Arm.post s s' := by
  have hB : BITS = 1280 := rfl
  have hsc_in : (⟨State.addr (s.gpr .r1), 32⟩ : Region) ∈ s.rd ++ s.wr := by rw [hp.rd]; simp
  have hpt_in : (⟨State.addr (s.gpr .r2), 32⟩ : Region) ∈ s.rd ++ s.wr := by rw [hp.rd]; simp
  unfold x25519Umaal
  refine WP.seq (WP.mono (setup_ok hp) fun s1 ⟨hc1, h12, h1, h2, hsv1, hf1, hr1⟩ => ?_)
  -- The scalar and the u-coordinate are as they were.
  have hk : bytesAt s1.mem (State.addr (s.gpr .r1)) 32 = bytesAt s.mem (State.addr (s.gpr .r1)) 32 :=
    bytesAt_frame hf1 fun r hr => by
      rw [List.mem_singleton.mp hr]; exact hp.sc_ws.sub_right (Region.sub_prefix (by decide))
  refine WP.seq (WP.mono (bits_ok hc1 h1 hp.f1 (by rw [hr1.rd, hr1.wr]; exact hsc_in) hp.sc_ws)
    fun s2 ⟨hc2, hr2, hf2, hb2⟩ => ?_)
  rw [hk] at hb2
  have hu : bytesAt s2.mem (State.addr (s.gpr .r2)) 32 = bytesAt s.mem (State.addr (s.gpr .r2)) 32 := by
    rw [bytesAt_frame hf2 fun r hr => by
        rw [List.mem_singleton.mp hr]; exact hp.pt_ws.sub_right (Offset.sub_base _ (by decide)),
      bytesAt_frame hf1 fun r hr => by
        rw [List.mem_singleton.mp hr]; exact hp.pt_ws.sub_right (Region.sub_prefix (by decide))]
  refine WP.seq (WP.mono (init_ok hc2 (o := s.gpr .r0) (pt := s.gpr .r2) (by rw [hr2.gpr _ (by decide), h12])
    (by rw [hr2.gpr _ (by decide), h2]) hp.f2 (by rw [hr2.rd, hr2.wr, hr1.rd, hr1.wr]; exact hpt_in) hp.pt_ws)
    fun s3 ⟨k3, hf3, ho3, hS3⟩ => ?_)
  rw [hu] at hS3
  have hc3 := k3.ctx hc2
  have hb3 := Bits.frame' hb2 hf3 (by decide)
  refine WP.seq (WP.mono (ladder_ok hc3 hb3 hS3) fun s4 ⟨k4, hf4, hc4, hsw4, hS4⟩ => ?_)
  refine WP.seq (WP.mono (lastSwap_ok hc4 (ladderAfter_swap_le _ _ (by decide)) hsw4 hS4)
    fun s5 ⟨k5, hf5, hS5⟩ => ?_)
  have hc5 := k5.ctx hc4
  refine WP.seq (WP.mono (invert_ok hc5 (hS5.mono (by decide) fun _ _ h => absurd h List.not_mem_nil))
    fun s6 ⟨k6, hf6, hc6, hS6⟩ => ?_)
  simp only [List.append_assoc]
  refine WP.append (mul_ok (o := X2) (a := X2) (c := R) (by decide) (by decide) (by decide) hc6)
    fun s7 ⟨k7, hf7, hv7, hl7⟩ => ?_
  have hc7 := k7.ctx hc6
  -- From `s3` to `s7` the code writes the field area only.
  have hfa : Frame [FAW (s.gpr .r3)] s3.mem s7.mem :=
    hf4.trans (hf5.trans (hf6.trans (hf7.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact Offset.sub _ (by decide) (by decide)⟩)))
  have ho7 : s7.mem.readW (State.addr (s.gpr .r3) + BitVec.ofNat 64 OUT) 32 = s.gpr .r0 := by
    rw [hfa.readW (Region.contains_self _ _) (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by decide)) (by decide) (by decide))
      (by decide)]
    exact ho3
  have hwr7 : s7.wr = s.wr := by rw [k7.wr, k6.wr, k5.wr, k4.wr, k3.wr, hr2.wr, hr1.wr]
  refine WP.append (output_ok hc7 hl7 ho7 (by rw [hwr7, hp.wr]; simp) hp.f0) fun s8 ⟨hbytes, k8, hf8⟩ => ?_
  have hsv8 : Saved9 (State.addr (s.gpr .r3)) s.gpr s8.mem := by
    refine (((hsv1.above hf2 (by decide) (by decide)).above hf3 (by decide) (by decide)).above hfa (by decide)
      (by decide)).frame hf8 fun r hr i hi => ?_
    rw [List.mem_singleton.mp hr]
    exact hp.out_ws.symm.sub_left (Offset.sub_base _ (by omega_using [hi]))
  refine WP.mono (restore_ok (k8.ctx hc7) hsv8) fun s9 ⟨hg9, hr9, hm9⟩ => ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hg9 0 (by decide)
    · exact hg9 1 (by decide)
    · exact hg9 2 (by decide)
    · exact hg9 3 (by decide)
    · exact hg9 4 (by decide)
    · exact hg9 5 (by decide)
    · exact hg9 6 (by decide)
    · exact hg9 7 (by decide)
    · exact hg9 8 (by decide)
  · rw [hr9.sp, k8.sp, k7.sp, k6.sp, k5.sp, k4.sp, k3.sp, hr2.sp, hr1.sp]
  · -- The result.
    show bytesAt s9.mem _ 32 = _
    rw [hm9, hbytes, VG.Proof.X25519.x25519_eq]
    have e7 := toFe_mul hv7
    rw [(hS6 X2 (by decide)).2.1, (hS6 R (by decide)).2.1] at e7
    rw [← VG.Proof.X25519.toFe_val, ← VG.Proof.X25519.encodeUCoordinate_eq, e7]
    simp only [upd, swapV, ladV, sel, iteT, VG.Proof.X25519.invert_eq, VG.Proof.X25519.pow_pw, cswap_fst,
      X1, X2, Z2, X3, Z3, R, Nat.reduceEqDiff, ite_false]

/-! ## Verified -/

theorem umaalTaint_wf {s : State} (hp : XPre s) : VG.Arm.Taint.Wf umaalTaint s := by
  refine ⟨fun _ => ⟨by simp [hp.wr, umaalTaint], ?_, ?_⟩, fun p hp' => ?_, fun h => absurd h (by decide),
    fun _ h => (List.not_mem_nil h).elim⟩
  · simp only [hp.wr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq,
      List.Pairwise.nil, false_implies, implies_true, and_true]
    exact hp.out_ws
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [addr_toNat]
    · exact hp.f0
    · exact hp.f3
  · simp only [umaalTaint, List.mem_singleton] at hp'; subst hp'
    simp [VG.Arm.Taint.region, hp.wr]

/-- Two runs agree on `umaalTaint` when they agree on the arguments. -/
theorem umaalTaint_agree {s t : State} (hs : XPre s) (ht : XPre t) (h : x25519Arm.pub s t) :
    VG.Arm.Taint.Agree umaalTaint s t := by
  obtain ⟨_, h0, h1, h2, h3⟩ := h
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => by rw [hs.wr, ht.wr, h0, h3], umaalTaint_wf hs,
    umaalTaint_wf ht, fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun h => absurd h (by decide), fun _ h => absurd h (Nat.not_lt_zero _)⟩
  simp only [umaalTaint, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact h0
  · exact h1
  · exact h2
  · exact h3

theorem x25519Umaal_ok (s : State) (hs : x25519Arm.pre s) :
    ∃ t s', Exec isa x25519Umaal s t s' ∧ abiPreserved s s' ∧ x25519Arm.post s s' :=
  x25519Umaal_correct (XPre.of hs)

theorem x25519Umaal_ct' : ConstantTime isa x25519Arm.pre x25519Arm.pub x25519Umaal :=
  x25519Umaal_ct fun _ _ h₁ h₂ hp => umaalTaint_agree (XPre.of h₁) (XPre.of h₂) hp

theorem x25519Umaal_verified : Verified Arm.target x25519Umaal (Proof.X25519.x25519Contract Arm.abi) :=
  Verified.of_correct x25519Umaal_ok x25519Umaal_ct' (by
    sig_implies [Proof.X25519.x25519Contract, Proof.X25519.x25519Sig, Proof.X25519.Arm.x25519Arm, Arm.abi,
      Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] [Proof.X25519.Arm.x25519Sat,
      Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using Proof.X25519.Arm.x25519Sat)

end VG.Proof.X25519.Arm.Words
