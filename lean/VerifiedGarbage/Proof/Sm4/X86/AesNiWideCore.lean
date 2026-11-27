module

public import VerifiedGarbage.Proof.Sm4.X86.AesNiWideMaps
public import VerifiedGarbage.Proof.Sm4.X86.AesNiCore
public import VerifiedGarbage.Spec.Sm4.Cbc
public import VerifiedGarbage.Proof.Modes.X86.Core
public import VerifiedGarbage.Proof.Framework.X86.SymFrame
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.X86.Sse
import VerifiedGarbage.Proof.Framework.X86.SseDword
import VerifiedGarbage.Proof.Framework.X86.SseRegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Sm4.CtrCipher
import VerifiedGarbage.Proof.Sm4.Layout

/-!
# SM4's core by the AES S-box, four blocks at a time, on x86 (32-bit)

`coreSpec d`: `Impl.Sm4.X86.AesNiWide.core d` meets what the modes need of a
core (`Proof.Modes.X86.CoreSpec`), with the key a schedule, read through the
first stack argument (the one-block core's `KeyArgs`), and its cipher
`Spec.Sm4.cipher` for encryption and `Spec.Sm4.invCipher` for decryption.

The proof is the one-block core's (`AesNiCore.lean`), a lane at a time: a
register holds a word of four blocks, block `l`'s in lane `l` (`Hw`, `Hk`,
`WordAt`), and the round's sum at a byte is that core's sum of the bytes of
its lane (`sig_lane`), since the shuffle before `aesenclast` undoes its
ShiftRows; so `sig_eq`, and a round of the code is `Spec.Sm4.round` in every
lane (`round_ok`). `crypt_wp`: the four blocks at byte 624 of the scratch
buffer are replaced with `Spec.Sm4.crypt` of them, under the round keys in
their places, in the order the rounds read them. `prepare_wp`: `prepare d`
leaves the schedule's round keys there in `d`'s order (`pos d`), the
reverse for decryption, which is the specification's decryption (§7.2).
-/

@[expose] public section

namespace VG.Proof.Sm4.X86.AesNiWide

open VG VG.X86 VG.X86.ByteMap VG.Impl.Sm4.X86.AesNiWide
open VG.Impl.Sm4.X86 (Dir)
open VG.Impl.Sm4.X86.AesNi (oE oH oCV oIV oK oM0 oR tbr kr m0)
open VG.Proof.Modes.X86 (ScrIn)
open VG.Spec.Sm4 (Word)
open VG.Proof.Sm4 (byteAt getLsbD_byteAt)
open VG.Proof.Sm4.X86.AesNi (tblAt var kv br cterms maskOk regs₀ am pl pv pk nm wl wk wl_xor wk_eq pv_pl kb sAt
  KeyAt frame_sAt frame_sAt_list st st_succ wp_ldx wp_stx wp_addi_x wp_subi_x cterms_sum byteAt_wordAt blockAt_getD
  next_in wk_sum srow_mod br_mod rkAt byteAt_rkAt Sch)

/-! ## A lane's bytes -/

/-- A register that holds, in lane `l`, the word `X l` in the rounds' form:
block `l`'s; and one that holds `aesenclast`'s input for the words `Y`. -/
def Hw (v : BitVec 128) (X : Nat → Word) : Prop := ∀ q < 16, byte v q = wl (X (q / 4)) q
def Hk (v : BitVec 128) (Y : Nat → Word) : Prop := ∀ q < 16, byte v q = wk (Y (q / 4)) q

/-- A round's sum at byte `q`, of `aesenclast`'s input bytes `w` before the
shuffle that undoes its ShiftRows. -/
def sig (w : Nat → Byte) (q : Nat) : Byte :=
  am oE (aesSbox (w q)) ^^^ am oH (aesSbox (w q)) ^^^ am oE (aesSbox (w (br 1 q))) ^^^
    am oE (aesSbox (w (br 2 q))) ^^^ am oH (aesSbox (w (br 3 q)))

/-- The sum at a byte is the one-block round's, of the bytes of its lane in
every lane. -/
theorem sig_lane (w : Nat → Byte) (q : Nat) : sig w q = AesNi.sig (fun p => w (4 * (q / 4) + p % 4)) q := by
  have e0 : 4 * (q / 4) + srow q % 4 = q := by rw [srow_mod]; exact Nat.div_add_mod q 4
  have ek : ∀ k, 4 * (q / 4) + srow (br k q) % 4 = br k q := fun k => by rw [srow_mod, br_mod]; rfl
  simp only [sig, AesNi.sig, e0, ek]

/-- A round's sum, of `aesenclast`'s input for the words `Y`, is `T(Y l)` in
the rounds' form, in every lane `l`. -/
theorem sig_eq {w : Nat → Byte} {Y : Nat → Word} (hw : ∀ p < 16, w p = wk (Y (p / 4)) p) {q : Nat} (hq : q < 16) :
    sig w q = wl (Spec.Sm4.t (Y (q / 4))) q := by
  rw [sig_lane]
  refine AesNi.sig_eq (fun p _ => ?_) q
  rw [hw _ (by omega_using [hq]), wk, wk, show (4 * (q / 4) + p % 4) / 4 = q / 4 by omega_arith,
    show (4 * (q / 4) + p % 4) % 4 = p % 4 by omega_arith]

/-- The word a round makes, in every lane. -/
def nw (x0 x1 x2 x3 : Nat → Word) (k : Word) : Nat → Word := fun l =>
  x0 l ^^^ Spec.Sm4.t (x1 l ^^^ x2 l ^^^ x3 l ^^^ k)

/-! ## What the parts of the code compute -/

/-- What a round needs of the state: the table's address in its register,
the scratch buffer's first 96 bytes, which end with the ring, readable, and
the mask. -/
structure Env (s : State) : Prop where
  tb : s.gpr tbr = s.syms tableName
  fit : (s.gpr Impl.Modes.X86.sb).toNat + 96 ≤ 2 ^ 32
  acc : ∀ o, o + 16 ≤ 96 → InRegions (s.rd ++ s.wr) (addr (s.gpr Impl.Modes.X86.sb) o) 16
  msk : ∀ i < 16, byte (s.xmm m0) i = 0x0f#8

section
variable {s : State}

theorem Env.rel (h : Env s) : Rel params (envOf params s) regs₀ s :=
  (rel_init (p := params) h.tb h.fit h.acc).const m0 h.msk

theorem env_var (p : Params) (r : XReg) {q : Nat} (hq : q < 16) :
    mask (envOf p s) (var r q) nvars = byte (s.xmm r) q := by
  have hr : r.ctorIdx < 8 := by cases r <;> decide
  rw [var, mask_bit _ (by show 16 * r.ctorIdx + q < 1024; omega_using [hr, hq]), envOf_reg p s r hq]

theorem env_key {o : Nat} (ho : o < 96) : mask (envOf params s) (kv o) nvars = kb s o := by
  rw [kv, mask_bit _ (by show 128 + o < 1024; omega_using [ho]), envOf_key]; rfl

theorem aT_sum (env : Nat → BitVec 8) (t : Nat) (a : XReg) (p : Nat) :
    sum env (aT t a p) = am t (aesSbox (mask env (var a p) nvars)) := by
  simp only [aT, sum, BitVec.xor_zero]; rfl

theorem sigma_sum (a : XReg) {q : Nat} (hq : q < 16) :
    sum (envOf params s) (sigma a q) = sig (fun p => byte (s.xmm a) p) q := by
  have b : ∀ k, br k q < 16 := fun k => by unfold br; omega_using [hq]
  simp only [sigma, sum_append, aT_sum, sig, env_var params a hq, env_var params a (b _)]

/-- A round but its key's load and its word's store: what it leaves in `c`
and in `e`, of the bytes it starts with. -/
theorem roundX_wp {a c n e : XReg} {s0 s2 : Nat} (hok : roundOk a c n e s0 s2 = true) (h0 : s0 + 16 ≤ 96)
    (h2 : s2 + 16 ≤ 96) (he : Env s) :
    WP isa (.block (roundX a c n e s0 s2)) s fun s' =>
      Same s s' ∧
      (∀ q < 16, byte (s'.xmm c) q = kb s (s0 + q) ^^^ byte (s.xmm e) q ^^^ kb s (s2 + q) ^^^
        byte (s.xmm n) q ^^^ sig (fun p => byte (s.xmm a) p) q) ∧
      (∀ q < 16, byte (s'.xmm e) q = kb s (s0 + q) ^^^ sig (fun p => byte (s.xmm a) p) q) ∧
      (∀ q < 16, byte (s'.xmm m0) q = 0x0f#8) := by
  unfold roundOk at hok
  split at hok <;> [cases hok; rename_i ρ hrun]
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hok
  obtain ⟨⟨⟨⟨hc, hes⟩, cc⟩, ce⟩, cm⟩ := hok
  refine run_wp he.rel hrun fun s' hr hsame => ?_
  simp only [maskOk, Bool.and_eq_true, Bool.not_eq_true'] at cm
  refine ⟨hsame, fun q hq => ?_, fun q hq => ?_, fun q hq => ?_⟩
  · rw [hr.bytes hc q hq, BV.same_eval _ (List.all_eq_true.mp cc q (List.mem_range.mpr hq))]
    simp only [BV.eval, mask_xor, sigma_sum a hq, BitVec.xor_zero,
      env_key (show s0 + q < 96 by omega_using [h0, hq]), env_key (show s2 + q < 96 by omega_using [h2, hq]),
      env_var params n hq, env_var params e hq]
  · rw [hr.bytes hes q hq, BV.same_eval _ (List.all_eq_true.mp ce q (List.mem_range.mpr hq))]
    simp only [BV.eval, sigma_sum a hq, BitVec.xor_zero, env_key (show s0 + q < 96 by omega_using [h0, hq])]
  · rw [hr.bytes cm.1 q hq, BV.same_eval _ (List.all_eq_true.mp cm.2 q (List.mem_range.mpr hq)), BV.cst_eval]

end

/-! ## The ring and the stores -/

/-- The ring's place `j` holds the words `X`: block `l`'s in lane `l`. -/
def WordAt (m : Mem) (B : BitVec 32) (j : Nat) (X : Nat → Word) : Prop :=
  ∀ q < 16, sAt m B (32 + 16 * j + q) = wl (X (q / 4)) q

theorem WordAt.frame {m m' : Mem} {B : BitVec 32} {i j : Nat} {X : Nat → Word} (h : WordAt m B i X)
    (hf : Frame [⟨B.setWidth 64 + BitVec.ofNat 64 (32 + 16 * j), 16⟩] m m') (hi : i < 4) (hj : j < 4)
    (hne : i ≠ j) : WordAt m' B i X := fun q hq => by
  rw [frame_sAt hf (by omega_using [hq, hne]) (by omega_using [hi, hq]) (by omega_using [hj])]; exact h q hq

/-- The ring's places are in the ring. -/
theorem ring_sub (B : BitVec 32) {j : Nat} (hj : j < 4) :
    Region.Sub ⟨B.setWidth 64 + BitVec.ofNat 64 (32 + 16 * j), 16⟩ ⟨B.setWidth 64 + BitVec.ofNat 64 32, 64⟩ :=
  Offset.sub _ (by omega_arith) (by omega_using [hj])

/-- A register stored at byte `o` of the scratch buffer: its bytes there,
and nothing else changed. -/
theorem store_sAt (m : Mem) {B : BitVec 32} {o : Nat} (hf : B.toNat + o + 16 ≤ 2 ^ 32) (v : BitVec 128) :
    (∀ q < 16, sAt (m.writeW (addr B o) v) B (o + q) = byte v q) ∧
      Frame [⟨B.setWidth 64 + BitVec.ofNat 64 o, 16⟩] m (m.writeW (addr B o) v) := by
  have ha : addr B o = B.setWidth 64 + BitVec.ofNat 64 o := addr_eq (by omega_using [hf])
  refine ⟨fun q hq => ?_, ?_⟩
  · show (m.writeW (addr B o) v) (B.setWidth 64 + BitVec.ofNat 64 (o + q)) = _
    rw [← Offset.add_ofNat_add_ofNat, ← ha,
      ← byte_readW (m.writeW (addr B o) v) (addr B o) (w := 128) (k := q) (by omega_using [hq]),
      Mem.readW_writeW_self _ _ 16 _ (by decide)]
    rfl
  · rw [ha]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ 16)

/-- Four registers to four places of the scratch buffer (`stores`): their
bytes there, and nothing else changed. -/
theorem stores_wp {s : State} {B : BitVec 32} {o : Nat} {r0 r1 r2 r3 : XReg} (hB : s.gpr Impl.Modes.X86.sb = B)
    (hwr : (⟨B.setWidth 64, 4 * 182⟩ : Region) ∈ s.wr) (hf : B.toNat + 728 ≤ 2 ^ 32) (ho : o + 64 ≤ 728) :
    WP isa (.block (stores o r0 r1 r2 r3)) s fun s' =>
      s'.gpr = s.gpr ∧ s'.xmm = s.xmm ∧ s'.zf = s.zf ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.syms = s.syms ∧
      Frame [⟨B.setWidth 64 + BitVec.ofNat 64 o, 64⟩] s.mem s'.mem ∧
      (∀ q < 16, sAt s'.mem B (o + q) = byte (s.xmm r0) q) ∧
      (∀ q < 16, sAt s'.mem B (o + 16 + q) = byte (s.xmm r1) q) ∧
      (∀ q < 16, sAt s'.mem B (o + 32 + q) = byte (s.xmm r2) q) ∧
      (∀ q < 16, sAt s'.mem B (o + 48 + q) = byte (s.xmm r3) q) := by
  have hin : ∀ d, d + 16 ≤ 728 → InRegions s.wr (addr B d) 16 := fun d hd => ⟨_, hwr, by
    rw [addr_eq (by omega_using [hf, hd])]; exact Offset.contains_base _ (by omega_using [hd]) (by omega_using [hd])⟩
  obtain ⟨v0, f0⟩ := store_sAt s.mem (B := B) (o := o) (by omega_using [hf, ho]) (s.xmm r0)
  obtain ⟨v1, f1⟩ := store_sAt (s.mem.writeW (addr B o) (s.xmm r0)) (B := B) (o := o + 16)
    (by omega_using [hf, ho]) (s.xmm r1)
  obtain ⟨v2, f2⟩ := store_sAt ((s.mem.writeW (addr B o) (s.xmm r0)).writeW (addr B (o + 16)) (s.xmm r1)) (B := B)
    (o := o + 32) (by omega_using [hf, ho]) (s.xmm r2)
  obtain ⟨v3, f3⟩ := store_sAt (((s.mem.writeW (addr B o) (s.xmm r0)).writeW (addr B (o + 16)) (s.xmm r1)).writeW
    (addr B (o + 32)) (s.xmm r2)) (B := B) (o := o + 48) (by omega_using [hf, ho]) (s.xmm r3)
  have hb : ∀ d, d < 728 → d < 2 ^ 32 := fun d hd => by omega_using [hd]
  unfold stores
  refine wp_stx (by rw [hB]; exact hin _ (by omega_using [ho])) ?_
  refine wp_stx (s := { s with mem := _ }) (by show InRegions s.wr (addr (s.gpr _) _) 16; rw [hB]; exact hin _ (by omega_using [ho])) ?_
  refine wp_stx (s := { s with mem := _ }) (by show InRegions s.wr (addr (s.gpr _) _) 16; rw [hB]; exact hin _ (by omega_using [ho])) ?_
  refine wp_stx (s := { s with mem := _ }) (by show InRegions s.wr (addr (s.gpr _) _) 16; rw [hB]; exact hin _ (by omega_using [ho])) (WP.block_nil ?_)
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, fun q hq => ?_, fun q hq => ?_, fun q hq => ?_, fun q hq => ?_⟩
  · show Frame _ s.mem ((((s.mem.writeW (addr (s.gpr _) o) (s.xmm r0)).writeW (addr (s.gpr _) (o + 16)) (s.xmm r1)).writeW
      (addr (s.gpr _) (o + 32)) (s.xmm r2)).writeW (addr (s.gpr _) (o + 48)) (s.xmm r3))
    rw [hB]
    have sub : ∀ d, d + 16 ≤ 64 → ∀ r ∈ [(⟨B.setWidth 64 + BitVec.ofNat 64 (o + d), 16⟩ : Region)],
        ∃ r' ∈ [(⟨B.setWidth 64 + BitVec.ofNat 64 o, 64⟩ : Region)], Region.Sub r r' := fun d hd r hr => by
      rw [List.mem_singleton.mp hr]
      exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by omega_arith) (by omega_using [hd])⟩
    exact (((f0.sub (sub 0 (by decide))).trans (f1.sub (sub 16 (by decide)))).trans
      (f2.sub (sub 32 (by decide)))).trans (f3.sub (sub 48 (by decide)))
  · show sAt ((((s.mem.writeW (addr (s.gpr _) o) (s.xmm r0)).writeW (addr (s.gpr _) (o + 16)) (s.xmm r1)).writeW
      (addr (s.gpr _) (o + 32)) (s.xmm r2)).writeW (addr (s.gpr _) (o + 48)) (s.xmm r3)) B (o + q) = _
    rw [hB, frame_sAt f3 (by omega_using [hq]) (hb _ (by omega_using [ho, hq])) (hb _ (by omega_using [ho])),
      frame_sAt f2 (by omega_using [hq]) (hb _ (by omega_using [ho, hq])) (hb _ (by omega_using [ho])),
      frame_sAt f1 (by omega_using [hq]) (hb _ (by omega_using [ho, hq])) (hb _ (by omega_using [ho]))]
    exact v0 q hq
  · show sAt ((((s.mem.writeW (addr (s.gpr _) o) (s.xmm r0)).writeW (addr (s.gpr _) (o + 16)) (s.xmm r1)).writeW
      (addr (s.gpr _) (o + 32)) (s.xmm r2)).writeW (addr (s.gpr _) (o + 48)) (s.xmm r3)) B (o + 16 + q) = _
    rw [hB, frame_sAt f3 (by omega_using [hq]) (hb _ (by omega_using [ho, hq])) (hb _ (by omega_using [ho])),
      frame_sAt f2 (by omega_using [hq]) (hb _ (by omega_using [ho, hq])) (hb _ (by omega_using [ho]))]
    exact v1 q hq
  · show sAt ((((s.mem.writeW (addr (s.gpr _) o) (s.xmm r0)).writeW (addr (s.gpr _) (o + 16)) (s.xmm r1)).writeW
      (addr (s.gpr _) (o + 32)) (s.xmm r2)).writeW (addr (s.gpr _) (o + 48)) (s.xmm r3)) B (o + 32 + q) = _
    rw [hB, frame_sAt f3 (by omega_using [hq]) (hb _ (by omega_using [ho, hq])) (hb _ (by omega_using [ho]))]
    exact v2 q hq
  · show sAt ((((s.mem.writeW (addr (s.gpr _) o) (s.xmm r0)).writeW (addr (s.gpr _) (o + 16)) (s.xmm r1)).writeW
      (addr (s.gpr _) (o + 32)) (s.xmm r2)).writeW (addr (s.gpr _) (o + 48)) (s.xmm r3)) B (o + 48 + q) = _
    rw [hB]
    exact v3 q hq

/-- A state of `crypt` after `n` turns, from the state `s₀` it starts in:
the scratch buffer's address, the round keys' pointer, and the table's
address. -/
structure At (s₀ : State) (B : BitVec 32) (n : Nat) (s : State) : Prop where
  base : s.gpr Impl.Modes.X86.sb = B
  esp : s.gpr .esp = s₀.gpr .esp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  syms : s.syms = s₀.syms
  tb : s.gpr tbr = s₀.syms tableName
  kp : s.gpr kr = B + BitVec.ofNat 32 (96 + 64 * n)

section
variable {s₀ s : State} {B : BitVec 32} {n : Nat}

theorem At.of_gpr {s' : State} (h : At s₀ B n s) (hg : s'.gpr = s.gpr) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsy : s'.syms = s.syms) : At s₀ B n s' :=
  ⟨by rw [hg]; exact h.base, by rw [hg]; exact h.esp, hrd.trans h.rd, hwr.trans h.wr, hsy.trans h.syms,
    by rw [hg]; exact h.tb, by rw [hg]; exact h.kp⟩

theorem At.kr64 (h : At s₀ B n s) (hf : B.toNat + 728 ≤ 2 ^ 32) (hn : n ≤ 8) :
    (s.gpr kr).setWidth 64 = B.setWidth 64 + BitVec.ofNat 64 (96 + 64 * n) := by
  rw [h.kp]; exact addr_eq (by omega_using [hf, hn])

theorem At.krNat (h : At s₀ B n s) (hf : B.toNat + 728 ≤ 2 ^ 32) (hn : n ≤ 8) :
    (s.gpr kr).toNat = B.toNat + (96 + 64 * n) := by
  rw [h.kp, Offset.toNat_add_ofNat, Nat.mod_eq_of_lt (a := 96 + 64 * n) (by omega_using [hn]),
    Nat.mod_eq_of_lt (by omega_using [hf, hn])]

theorem At.scr (h : At s₀ B n s) (o : Nat) : kb s o = sAt s.mem B o := by
  rw [kb, h.base]; rfl

theorem At.env (h : At s₀ B n s) (hs : ScrIn s₀ B 182) (hm : ∀ q < 16, byte (s.xmm m0) q = 0x0f#8) : Env s := by
  have hf : B.toNat + 728 ≤ 2 ^ 32 := hs.fit
  refine ⟨by rw [h.tb, h.syms], by rw [h.base]; omega_using [hf],
    fun o ho => ⟨_, List.mem_append_right _ (by rw [h.wr]; exact hs.wr), ?_⟩, hm⟩
  rw [h.base, addr_eq (by omega_using [hf, ho])]
  exact Offset.contains_base _ (by omega_using [ho]) (by omega_using [ho])

/-- Round `j` of turn `n`: round `4 n + j` of the four blocks. -/
theorem round_ok {a c nr e : XReg} {j : Nat}
    (hok : roundOk a c nr e (oR + 16 * j) (oR + 16 * ((j + 2) % 4)) = true) (hj : j < 4) (hea : ¬a = e)
    (hen : ¬nr = e) (hem : ¬m0 = e) (hs : ScrIn s₀ B 182) (hn : n < 8) (h : At s₀ B n s)
    (hm : ∀ q < 16, byte (s.xmm m0) q = 0x0f#8) {x0 x1 x2 x3 : Nat → Word} {k : Word}
    (hin : Hk (s.xmm a) (fun l => x1 l ^^^ x2 l ^^^ x3 l ^^^ k)) (hx3 : Hw (s.xmm nr) x3)
    (w0 : WordAt s.mem B j x0) (w2 : WordAt s.mem B ((j + 2) % 4) x2) :
    WP isa (.block (round a c nr e j)) s fun s' =>
      At s₀ B n s' ∧ (∀ q < 16, byte (s'.xmm m0) q = 0x0f#8) ∧ s'.gpr = s.gpr ∧ s'.zf = s.zf ∧
      Frame [⟨B.setWidth 64 + BitVec.ofNat 64 (32 + 16 * j), 16⟩] s.mem s'.mem ∧
      Hw (s'.xmm e) (nw x0 x1 x2 x3 k) ∧ WordAt s'.mem B j (nw x0 x1 x2 x3 k) ∧
      ∀ k', KeyAt s.mem B (4 * n + j + 1) k' → Hk (s'.xmm c) (fun l => x2 l ^^^ x3 l ^^^ nw x0 x1 x2 x3 k l ^^^ k') := by
  have hf : B.toNat + 728 ≤ 2 ^ 32 := hs.fit
  have hle := Nat.le_of_lt hn
  have hkn := h.krNat hf hle
  show WP isa (.block (.movdquLoad e ⟨kr, 16 * j + 16⟩ ::
    (roundX a c nr e (oR + 16 * j) (oR + 16 * ((j + 2) % 4)) ++
      [.movdquStore ⟨Impl.Modes.X86.sb, 32 + 16 * j⟩ e]))) s _
  -- the next round's key
  have hl : InRegions (s.rd ++ s.wr) (addr (s.gpr kr) (16 * j + 16)) 16 :=
    ⟨_, List.mem_append_right _ (by rw [h.wr]; exact hs.wr), by
      rw [addr_eq (by omega_using [hkn, hf, hn, hj]), h.kr64 hf hle, Offset.add_ofNat_add_ofNat]
      exact Offset.contains_base _ (by omega_using [hn, hj]) (by omega_using [hn, hj])⟩
  refine wp_ldx hl ?_
  obtain ⟨s₁, hs₁⟩ : ∃ s₁, s₁ = s.setXmm e (s.mem.readW (addr (s.gpr kr) (16 * j + 16)) 128) := ⟨_, rfl⟩
  rw [← hs₁]
  have a₁ : At s₀ B n s₁ := by subst hs₁; exact h.of_gpr rfl rfl rfl rfl
  have g₁ : s₁.gpr = s.gpr := by subst hs₁; rfl
  have z₁ : s₁.zf = s.zf := by subst hs₁; rfl
  have m₁ : s₁.mem = s.mem := by subst hs₁; rfl
  have xa : s₁.xmm a = s.xmm a := by subst hs₁; exact RegUpd.xmm_setXmm_of_ne _ _ hea
  have xn : s₁.xmm nr = s.xmm nr := by subst hs₁; exact RegUpd.xmm_setXmm_of_ne _ _ hen
  have xm : s₁.xmm m0 = s.xmm m0 := by subst hs₁; exact RegUpd.xmm_setXmm_of_ne _ _ hem
  have ke : ∀ q < 16, byte (s₁.xmm e) q = sAt s.mem B (96 + 16 * (4 * n + j + 1) + q) := fun q hq => by
    subst hs₁
    rw [RegUpd.xmm_setXmm_self]
    show (s.mem.readW (addr (s.gpr kr) (16 * j + 16)) 128).extractLsb' (8 * q) 8 = _
    rw [byte_readW _ _ (by omega_using [hq]), addr_eq (by omega_using [hkn, hf, hn, hj]), h.kr64 hf hle,
      Offset.add_ofNat_add_ofNat, Offset.add_ofNat_add_ofNat, sAt,
      show 96 + 16 * (4 * n + j + 1) + q = 96 + 64 * n + (16 * j + 16 + q) by omega_arith]
  have s0le : oR + 16 * j + 16 ≤ 96 := by show 32 + 16 * j + 16 ≤ 96; omega_using [hj]
  have s2le : oR + 16 * ((j + 2) % 4) + 16 ≤ 96 := by show 32 + 16 * ((j + 2) % 4) + 16 ≤ 96; omega_arith
  refine WP.block_append_iff.mpr (WP.mono (roundX_wp hok s0le s2le
    (a₁.env hs fun q hq => by rw [xm]; exact hm q hq)) fun s₂ ⟨hsame, bc, be, bm⟩ => ?_)
  have sg : ∀ q < 16, sig (fun p => byte (s₁.xmm a) p) q =
      wl (Spec.Sm4.t (x1 (q / 4) ^^^ x2 (q / 4) ^^^ x3 (q / 4) ^^^ k)) q := fun q hq =>
    sig_eq (Y := fun l => x1 l ^^^ x2 l ^^^ x3 l ^^^ k) (fun p hp => by rw [xa]; exact hin p hp) hq
  have e0 : ∀ q < 16, kb s₁ (oR + 16 * j + q) = wl (x0 (q / 4)) q := fun q hq => by
    rw [a₁.scr, m₁]; exact w0 q hq
  have e2 : ∀ q < 16, kb s₁ (oR + 16 * ((j + 2) % 4) + q) = wl (x2 (q / 4)) q := fun q hq => by
    rw [a₁.scr, m₁]; exact w2 q hq
  obtain ⟨f, rfl⟩ := hsame
  have ev : ∀ q < 16, byte (f e) q = wl (nw x0 x1 x2 x3 k (q / 4)) q := fun q hq =>
    (be q hq).trans (by rw [e0 q hq, sg q hq, nw, wl_xor])
  -- the new word to its place
  have ha : addr B (32 + 16 * j) = B.setWidth 64 + BitVec.ofNat 64 (32 + 16 * j) :=
    addr_eq (by omega_using [hf, hj])
  have hwr : InRegions s₁.wr (addr (s₁.gpr Impl.Modes.X86.sb) (32 + 16 * j)) 16 :=
    ⟨_, by rw [a₁.wr]; exact hs.wr, by
      rw [a₁.base, ha]; exact Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj])⟩
  refine wp_stx (s := { s₁ with xmm := f }) hwr (WP.block_nil ?_)
  refine ⟨a₁.of_gpr rfl rfl rfl rfl, bm, g₁, z₁, ?_, ev, fun q hq => ?_, fun k' hk' q hq => ?_⟩
  · show Frame _ s.mem (s₁.mem.writeW (addr (s₁.gpr Impl.Modes.X86.sb) (32 + 16 * j)) (f e))
    rw [m₁, a₁.base, ha]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ 16)
  · show (s₁.mem.writeW (addr (s₁.gpr Impl.Modes.X86.sb) (32 + 16 * j)) (f e))
      (B.setWidth 64 + BitVec.ofNat 64 (32 + 16 * j + q)) = _
    rw [a₁.base, ← Offset.add_ofNat_add_ofNat, ← ha,
      ← byte_readW (s₁.mem.writeW (addr B (32 + 16 * j)) (f e)) (addr B (32 + 16 * j)) (w := 128) (k := q)
        (by omega_using [hq]),
      Mem.readW_writeW_self _ _ 16 _ (by decide)]
    exact ev q hq
  · refine (bc q hq).trans ?_
    rw [e0 q hq, ke q hq, e2 q hq, xn, hx3 q hq, sg q hq, hk' q hq]
    exact next_in _ _ _ _ _ _

end

/-! ## The four blocks -/

/-- Word `w` of block `l` of the scratch buffer's four. -/
def bwd (m : Mem) (B : BitVec 32) (w l : Nat) : Word :=
  Spec.Sm4.wordAt (Spec.Sm4.blockAt m (B.setWidth 64 + BitVec.ofNat 64 (624 + 16 * l))) (4 * w)

theorem byteAt_bwd (m : Mem) (B : BitVec 32) {w l k : Nat} (hw : w < 4) (hk : k < 4) :
    byteAt (bwd m B w l) k = sAt m B (624 + 16 * l + (4 * w + k)) := by
  rw [bwd, byteAt_wordAt _ _ hk, blockAt_getD _ _ (by omega_using [hw, hk]), Offset.add_ofNat_add_ofNat]; rfl

section
variable {s : State} {B : BitVec 32}

/-- The four blocks to their four words in the rounds' form, in `xmm0`,
`xmm3`, `xmm4` and `xmm1`; the exclusive-or of the last three in `xmm2`;
and the mask. -/
theorem head_wp (htb : s.gpr tbr = s.syms tableName) (hB : s.gpr Impl.Modes.X86.sb = B)
    (hwr : (⟨B.setWidth 64, 4 * 182⟩ : Region) ∈ s.wr) (hf : B.toNat + 728 ≤ 2 ^ 32) :
    WP isa (.block headX) s fun s' =>
      Same s s' ∧ Hw (s'.xmm .xmm0) (bwd s.mem B 0) ∧ Hw (s'.xmm .xmm3) (bwd s.mem B 1) ∧
      Hw (s'.xmm .xmm4) (bwd s.mem B 2) ∧ Hw (s'.xmm .xmm1) (bwd s.mem B 3) ∧
      (∀ q < 16, byte (s'.xmm .xmm2) q = wl (bwd s.mem B 1 (q / 4)) q ^^^ wl (bwd s.mem B 2 (q / 4)) q ^^^
        wl (bwd s.mem B 3 (q / 4)) q) ∧
      (∀ q < 16, byte (s'.xmm m0) q = 0x0f#8) := by
  have rel : Rel hparams (envOf hparams s) Regs.init s :=
    rel_init (p := hparams) htb (by show (s.gpr Impl.Modes.X86.sb).toNat + 688 ≤ _; rw [hB]; omega_using [hf])
      (fun o ho => ⟨_, List.mem_append_right _ hwr, by
        show Region.Contains _ (addr (s.gpr Impl.Modes.X86.sb) o) 16
        have ho' : o + 16 ≤ 688 := ho
        rw [hB, addr_eq (by omega_using [hf, ho'])]
        exact Offset.contains_base _ (by omega_using [ho']) (by omega_using [ho'])⟩)
  have hok := conv_all.1
  unfold headOk at hok
  split at hok <;> [cases hok; rename_i ρ hrun]
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hok
  obtain ⟨⟨⟨⟨⟨⟨h0, h3⟩, h4⟩, h1⟩, h2⟩, cx⟩, cm⟩ := hok
  refine run_wp rel hrun fun s' hr hsame => ?_
  simp only [maskOk, Bool.and_eq_true, Bool.not_eq_true'] at cm
  have ev : ∀ w < 4, ∀ q < 16, (hw w q).eval (envOf hparams s) = wl (bwd s.mem B w (q / 4)) q :=
    fun w hw4 q hq => by
    rw [hw, BV.eval, mask_zero, cterms_sum, BitVec.zero_xor, BitVec.xor_zero, kv,
      mask_bit _ (by show 128 + (624 + 16 * (q / 4) + 4 * w + q % 4) < 1024; omega_using [hw4, hq]), envOf_key,
      show (s.gpr hparams.kreg) = s.gpr Impl.Modes.X86.sb from rfl, hB, wl,
      byteAt_bwd _ _ hw4 (Nat.mod_lt _ (by decide)), sAt,
      show 624 + 16 * (q / 4) + (4 * w + q % 4) = oB + 16 * (q / 4) + 4 * w + q % 4 by show _ = 624 + _ + _ + _; omega_arith]
    rfl
  have cq := fun q (hq : q < 16) => List.all_eq_true.mp cx q (List.mem_range.mpr hq)
  simp only [Bool.and_eq_true] at cq
  refine ⟨hsame, fun q hq => ?_, fun q hq => ?_, fun q hq => ?_, fun q hq => ?_, fun q hq => ?_, fun q hq => ?_⟩
  · rw [hr.bytes h0 q hq, BV.same_eval _ (cq q hq).1.1.1.1, ev 0 (by decide) q hq]
  · rw [hr.bytes h3 q hq, BV.same_eval _ (cq q hq).1.1.1.2, ev 1 (by decide) q hq]
  · rw [hr.bytes h4 q hq, BV.same_eval _ (cq q hq).1.1.2, ev 2 (by decide) q hq]
  · rw [hr.bytes h1 q hq, BV.same_eval _ (cq q hq).1.2, ev 3 (by decide) q hq]
  · rw [hr.bytes h2 q hq, BV.same_eval _ (cq q hq).2, BV.xor_eval, BV.xor_eval, ev 1 (by decide) q hq,
      ev 2 (by decide) q hq, ev 3 (by decide) q hq]
  · rw [hr.bytes cm.1 q hq, BV.same_eval _ (List.all_eq_true.mp cm.2 q (List.mem_range.mpr hq)), BV.cst_eval]

end

section
variable {s₀ s : State} {B : BitVec 32} {rk : Nat → Word}

/-- The scratch buffer's four blocks to the ring, the registers of the
loop, and the first round's input. -/
theorem cryptHead_wp (hB : s.gpr Impl.Modes.X86.sb = B) (hs : ScrIn s B 182)
    (htab : s.mem.readW (B.setWidth 64) 32 = s.syms tableName) (hk : ∀ i < 32, KeyAt s.mem B i (rk i)) :
    WP isa (.block cryptHead) s fun s' =>
      At s B 0 s' ∧ (∀ q < 16, byte (s'.xmm m0) q = 0x0f#8) ∧ s'.gpr .eax = BitVec.ofNat 32 8 ∧
      Frame [⟨B.setWidth 64 + BitVec.ofNat 64 32, 64⟩] s.mem s'.mem ∧
      (∀ i < 32, KeyAt s'.mem B i (rk i)) ∧
      (∀ w < 4, WordAt s'.mem B w (bwd s.mem B w)) ∧ Hw (s'.xmm .xmm1) (bwd s.mem B 3) ∧
      Hk (s'.xmm .xmm0) (fun l => bwd s.mem B 1 l ^^^ bwd s.mem B 2 l ^^^ bwd s.mem B 3 l ^^^ rk 0) := by
  have hf : B.toNat + 728 ≤ 2 ^ 32 := hs.fit
  have hw : InRegions (s.rd ++ s.wr) (addr B 0) 4 := ⟨_, List.mem_append_right _ hs.wr, by
    rw [addr_eq (by omega_using [hf])]; exact Offset.contains_base _ (by decide) (by decide)⟩
  show WP isa (.block (.mov tbr (.mem ⟨Impl.Modes.X86.sb, 0⟩) :: .mov kr (.reg Impl.Modes.X86.sb) ::
    .alu .add kr (.imm 96) :: .mov .eax (.imm 8) ::
    (headX ++ (stores oR .xmm0 .xmm3 .xmm4 .xmm1 ++ cryptKey)))) s _
  refine Wp.wp_ldm hB hw fun s₁ u₁ => ?_
  refine Wp.wp_mov fun s₂ u₂ => ?_
  refine Wp.wp_addi fun s₃ u₃ => ?_
  refine Wp.wp_movi fun s₄ u₄ => ?_
  have e₄ : s₄.mem = s.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have r₄ : s₄.rd = s.rd := by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  have w₄ : s₄.wr = s.wr := by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  have y₄ : s₄.syms = s.syms := by rw [u₄.syms, u₃.syms, u₂.syms, u₁.syms]
  have b₄ : s₄.gpr Impl.Modes.X86.sb = B := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hB]
  have a₄ : At s B 0 s₄ := by
    refine ⟨b₄, ?_, r₄, w₄, y₄, ?_, ?_⟩
    · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
    · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr,
        addr_eq (by omega_using [hf]), BitVec.add_zero]
      exact htab
    · rw [u₄.other _ (by decide), u₃.gpr, u₂.gpr, u₁.other _ (by decide), hB]
      rfl
  have c₄ : s₄.gpr .eax = BitVec.ofNat 32 8 := by rw [u₄.gpr]; rfl
  refine WP.block_append_iff.mpr (WP.mono (head_wp (B := B) (by rw [a₄.tb, a₄.syms]) a₄.base
    (by rw [a₄.wr]; exact hs.wr) hf) fun s₅ ⟨hsame, x0₅, x3₅, x4₅, x1₅, x2₅, m₅⟩ => ?_)
  obtain ⟨f, rfl⟩ := hsame
  rw [e₄] at x0₅ x3₅ x4₅ x1₅ x2₅
  refine WP.block_append_iff.mpr (WP.mono (stores_wp (s := { s₄ with xmm := f }) (B := B) (o := oR) a₄.base
    (by show _ ∈ s₄.wr; rw [a₄.wr]; exact hs.wr) hf (by decide))
    fun s₆ ⟨g₆, x₆, _, rd₆, wr₆, sy₆, f₆, v0, v1, v2, v3⟩ => ?_)
  have a₆ : At s B 0 s₆ := a₄.of_gpr g₆ rd₆ wr₆ sy₆
  have f₆' : Frame [⟨B.setWidth 64 + BitVec.ofNat 64 32, 64⟩] s.mem s₆.mem := by
    have f' : Frame _ s₄.mem s₆.mem := f₆
    rwa [e₄] at f'
  have key₆ : ∀ i < 32, KeyAt s₆.mem B i (rk i) := fun i hi q hq => by
    have := f₆'.bytes (R := ⟨B.setWidth 64 + BitVec.ofNat 64 (96 + 16 * i + q), 1⟩) (fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact Offset.disjoint _ (.inr (by omega_arith)) (by omega_using [hi, hq]) (by decide))
      (show (1 : Nat) ≤ 2 ^ 64 by decide) (i := 0) (show (0 : Nat) < 1 by decide)
    rw [BitVec.add_zero] at this
    rw [sAt, this]
    exact hk i hi q hq
  have hkn := a₆.krNat hf (by decide)
  have hl₆ : InRegions (s₆.rd ++ s₆.wr) (addr (s₆.gpr kr) 0) 16 :=
    ⟨_, List.mem_append_right _ (by rw [a₆.wr]; exact hs.wr), by
      rw [addr_eq (by omega_using [hkn, hf]), a₆.kr64 hf (by decide), Offset.add_ofNat_add_ofNat]
      exact Offset.contains_base _ (by decide) (by decide)⟩
  show WP isa (.block [.movdquLoad .xmm0 ⟨kr, 0⟩, .xop (.bin .pxor .xmm0 .xmm2)]) s₆ _
  refine wp_ldx hl₆ (Wp.cons rfl (WP.block_nil ?_))
  have kq : ∀ q < 16, byte (s₆.mem.readW (addr (s₆.gpr kr) 0) 128) q = wk (rk 0) q := fun q hq => by
    show (s₆.mem.readW (addr (s₆.gpr kr) 0) 128).extractLsb' (8 * q) 8 = _
    rw [byte_readW _ _ (by omega_using [hq]), addr_eq (by omega_using [hkn, hf]), BitVec.add_zero,
      a₆.kr64 hf (by decide), Offset.add_ofNat_add_ofNat]
    exact key₆ 0 (by decide) q hq
  have x₆' : ∀ r, s₆.xmm r = f r := fun r => by rw [x₆]
  refine ⟨a₆.of_gpr rfl rfl rfl rfl, fun q hq => ?_, ?_, f₆', key₆, fun w hw4 q hq => ?_, fun q hq => ?_,
    fun q hq => ?_⟩
  · show byte (s₆.xmm m0) q = _
    rw [x₆']; exact m₅ q hq
  · show s₆.gpr .eax = _
    rw [g₆]; exact c₄
  · show sAt s₆.mem B (32 + 16 * w + q) = _
    rcases (show w = 0 ∨ w = 1 ∨ w = 2 ∨ w = 3 by omega_using [hw4]) with rfl | rfl | rfl | rfl
    · exact (v0 q hq).trans (x0₅ q hq)
    · exact (v1 q hq).trans (x3₅ q hq)
    · exact (v2 q hq).trans (x4₅ q hq)
    · exact (v3 q hq).trans (x1₅ q hq)
  · show byte (s₆.xmm .xmm1) q = _
    rw [x₆']; exact x1₅ q hq
  · show byte (s₆.mem.readW (addr (s₆.gpr kr) 0) 128 ^^^ s₆.xmm .xmm2) q = _
    rw [byte_xor, kq q hq, x₆', x2₅ q hq, BitVec.xor_comm]
    exact wk_sum _ _ _ _ _

/-- The state with `n` turns left: the keys' pointer after `8 - n` turns,
the turns left in `eax`, the round keys, and the four words of the
specification's state of each block after `4 (8 - n)` rounds in the ring,
the last also in `xmm1`, with `aesenclast`'s input for the next round in
`xmm0`. -/
def Inv (s₀ : State) (B : BitVec 32) (rk : Nat → Word) (b : Nat → Spec.Sm4.Block) (n : Nat) (s : State) : Prop :=
  n ≤ 8 ∧ At s₀ B (8 - n) s ∧ (∀ q < 16, byte (s.xmm m0) q = 0x0f#8) ∧ s.gpr .eax = BitVec.ofNat 32 n ∧
    Frame [⟨B.setWidth 64 + BitVec.ofNat 64 32, 64⟩] s₀.mem s.mem ∧ (∀ i < 32, KeyAt s.mem B i (rk i)) ∧
    ∃ x0 x1 x2 x3 : Nat → Word, (∀ l, st rk (b l) (4 * (8 - n)) = (x0 l, x1 l, x2 l, x3 l)) ∧
      WordAt s.mem B 0 x0 ∧ WordAt s.mem B 1 x1 ∧ WordAt s.mem B 2 x2 ∧ WordAt s.mem B 3 x3 ∧
      Hw (s.xmm .xmm1) x3 ∧ (1 ≤ n → Hk (s.xmm .xmm0) (fun l => x1 l ^^^ x2 l ^^^ x3 l ^^^ rk (4 * (8 - n))))

/-- A turn of the loop: four rounds. -/
theorem turn_wp (hs : ScrIn s₀ B 182) {b : Nat → Spec.Sm4.Block} {n : Nat} (hn : 1 ≤ n) (hI : Inv s₀ B rk b n s) :
    WP isa (.block turn) s fun s' => s'.zf = some (decide (n = 1)) ∧ Inv s₀ B rk b (n - 1) s' := by
  obtain ⟨hn8, a, hm, hc, hfr, hk, x0, x1, x2, x3, hst, w0, w1, w2, w3, hx3, hin⟩ := hI
  have hin := hin hn
  obtain ⟨m, hm'⟩ : ∃ m, m = 8 - n := ⟨_, rfl⟩
  rw [← hm'] at a hst hin
  have hm8 : m < 8 := by omega_using [hn, hm']
  show WP isa (.block (round .xmm0 .xmm4 .xmm1 .xmm2 0 ++ (round .xmm4 .xmm0 .xmm2 .xmm1 1 ++
    (round .xmm0 .xmm4 .xmm1 .xmm2 2 ++ (round .xmm4 .xmm0 .xmm2 .xmm1 3 ++ Impl.Sm4.X86.AesNiWide.step))))) s _
  -- round `4 m`
  refine WP.block_append_iff.mpr (WP.mono (round_ok (j := 0) (a := .xmm0) (c := .xmm4) (nr := .xmm1) (e := .xmm2)
    (round_all 0 (by decide)) (by decide) (by decide)
    (by decide) (by decide) hs hm8 a hm hin hx3 w0 w2) fun s₁ ⟨a₁, m₁, g₁, z₁, f₁, e₁, wn₁, c₁⟩ => ?_)
  obtain ⟨x4, hx4⟩ : ∃ x4, x4 = nw x0 x1 x2 x3 (rk (4 * m)) := ⟨_, rfl⟩
  rw [← hx4] at e₁ wn₁ c₁
  have k₁ : ∀ i < 32, KeyAt s₁.mem B i (rk i) := fun i hi => (hk i hi).frame f₁ (by omega_using [hi]) (by decide)
  have w1₁ : WordAt s₁.mem B 1 x1 := w1.frame f₁ (by decide) (by decide) (by decide)
  have w2₁ : WordAt s₁.mem B 2 x2 := w2.frame f₁ (by decide) (by decide) (by decide)
  have w3₁ : WordAt s₁.mem B 3 x3 := w3.frame f₁ (by decide) (by decide) (by decide)
  have in₁ := c₁ _ (hk (4 * m + 0 + 1) (by omega_using [hm8]))
  -- round `4 m + 1`
  refine WP.block_append_iff.mpr (WP.mono (round_ok (j := 1) (a := .xmm4) (c := .xmm0) (nr := .xmm2) (e := .xmm1)
    (round_all 1 (by decide)) (by decide) (by decide)
    (by decide) (by decide) hs hm8 a₁ m₁ in₁ e₁ w1₁ w3₁) fun s₂ ⟨a₂, m₂, g₂, z₂, f₂, e₂, wn₂, c₂⟩ => ?_)
  obtain ⟨x5, hx5⟩ : ∃ x5, x5 = nw x1 x2 x3 x4 (rk (4 * m + 0 + 1)) := ⟨_, rfl⟩
  rw [← hx5] at e₂ wn₂ c₂
  have k₂ : ∀ i < 32, KeyAt s₂.mem B i (rk i) := fun i hi => (k₁ i hi).frame f₂ (by omega_using [hi]) (by decide)
  have w0₂ : WordAt s₂.mem B 0 x4 := wn₁.frame f₂ (by decide) (by decide) (by decide)
  have w2₂ : WordAt s₂.mem B 2 x2 := w2₁.frame f₂ (by decide) (by decide) (by decide)
  have w3₂ : WordAt s₂.mem B 3 x3 := w3₁.frame f₂ (by decide) (by decide) (by decide)
  have in₂ := c₂ _ (k₁ (4 * m + 1 + 1) (by omega_using [hm8]))
  -- round `4 m + 2`
  refine WP.block_append_iff.mpr (WP.mono (round_ok (j := 2) (a := .xmm0) (c := .xmm4) (nr := .xmm1) (e := .xmm2)
    (round_all 2 (by decide)) (by decide) (by decide)
    (by decide) (by decide) hs hm8 a₂ m₂ in₂ e₂ w2₂ w0₂) fun s₃ ⟨a₃, m₃, g₃, z₃, f₃, e₃, wn₃, c₃⟩ => ?_)
  obtain ⟨x6, hx6⟩ : ∃ x6, x6 = nw x2 x3 x4 x5 (rk (4 * m + 1 + 1)) := ⟨_, rfl⟩
  rw [← hx6] at e₃ wn₃ c₃
  have k₃ : ∀ i < 32, KeyAt s₃.mem B i (rk i) := fun i hi => (k₂ i hi).frame f₃ (by omega_using [hi]) (by decide)
  have w0₃ : WordAt s₃.mem B 0 x4 := w0₂.frame f₃ (by decide) (by decide) (by decide)
  have w1₃ : WordAt s₃.mem B 1 x5 := wn₂.frame f₃ (by decide) (by decide) (by decide)
  have w3₃ : WordAt s₃.mem B 3 x3 := w3₂.frame f₃ (by decide) (by decide) (by decide)
  have in₃ := c₃ _ (k₂ (4 * m + 2 + 1) (by omega_using [hm8]))
  -- round `4 m + 3`
  refine WP.block_append_iff.mpr (WP.mono (round_ok (j := 3) (a := .xmm4) (c := .xmm0) (nr := .xmm2) (e := .xmm1)
    (round_all 3 (by decide)) (by decide) (by decide)
    (by decide) (by decide) hs hm8 a₃ m₃ in₃ e₃ w3₃ w1₃) fun s₄ ⟨a₄, m₄, g₄, z₄, f₄, e₄, wn₄, c₄⟩ => ?_)
  obtain ⟨x7, hx7⟩ : ∃ x7, x7 = nw x3 x4 x5 x6 (rk (4 * m + 2 + 1)) := ⟨_, rfl⟩
  rw [← hx7] at e₄ wn₄ c₄
  have k₄ : ∀ i < 32, KeyAt s₄.mem B i (rk i) := fun i hi => (k₃ i hi).frame f₄ (by omega_using [hi]) (by decide)
  have w0₄ : WordAt s₄.mem B 0 x4 := w0₃.frame f₄ (by decide) (by decide) (by decide)
  have w1₄ : WordAt s₄.mem B 1 x5 := w1₃.frame f₄ (by decide) (by decide) (by decide)
  have w2₄ : WordAt s₄.mem B 2 x6 := wn₃.frame f₄ (by decide) (by decide) (by decide)
  have c₀ : s₄.gpr .eax = BitVec.ofNat 32 n := by rw [g₄, g₃, g₂, g₁, hc]
  show WP isa (.block [.alu .add kr (.imm 64), .alu .sub .eax (.imm 1)]) s₄ _
  refine wp_addi_x fun s₅ u₅ x₅ => wp_subi_x fun s₆ u₆ x₆ z₆ => WP.block_nil ?_
  have e₆ : s₆.mem = s₄.mem := by rw [u₆.mem, u₅.mem]
  have xe : s₆.xmm = s₄.xmm := by rw [x₆, x₅]
  have c₅ : s₅.gpr .eax = BitVec.ofNat 32 n := by rw [u₅.other _ (by decide), c₀]
  refine ⟨?_, by omega_using [hn8], ?_, by rw [xe]; exact m₄, ?_, ?_, by rw [e₆]; exact k₄, x4, x5, x6, x7, ?_,
    by rw [e₆]; exact w0₄, by rw [e₆]; exact w1₄, by rw [e₆]; exact w2₄, by rw [e₆]; exact wn₄,
    by rw [xe]; exact e₄, fun h1 => ?_⟩
  · rw [z₆, c₅, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, Wp.sub_beq (by omega_using [hn8]) (by decide)]
  · rw [show 8 - (n - 1) = m + 1 by omega_using [hn, hm', hn8]]
    refine ⟨?_, ?_, by rw [u₆.rd, u₅.rd]; exact a₄.rd, by rw [u₆.wr, u₅.wr]; exact a₄.wr,
      by rw [u₆.syms, u₅.syms]; exact a₄.syms, ?_, ?_⟩
    · rw [u₆.other _ (by decide), u₅.other _ (by decide)]; exact a₄.base
    · rw [u₆.other _ (by decide), u₅.other _ (by decide)]; exact a₄.esp
    · rw [u₆.other _ (by decide), u₅.other _ (by decide)]; exact a₄.tb
    · rw [u₆.other _ (by decide), u₅.gpr, a₄.kp, show (64 : BitVec 32) = BitVec.ofNat 32 64 from rfl,
        Offset.add_ofNat_add_ofNat]
      congr 2
  · rw [u₆.gpr, c₅]; exact Wp.ofNat_pred hn
  · rw [e₆]
    exact (((hfr.trans (f₁.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact ring_sub B (by decide)⟩)).trans
      (f₂.sub fun r hr => ⟨_, List.mem_singleton_self _, by
        rw [List.mem_singleton.mp hr]; exact ring_sub B (by decide)⟩)).trans
      (f₃.sub fun r hr => ⟨_, List.mem_singleton_self _, by
        rw [List.mem_singleton.mp hr]; exact ring_sub B (by decide)⟩)).trans
      (f₄.sub fun r hr => ⟨_, List.mem_singleton_self _, by
        rw [List.mem_singleton.mp hr]; exact ring_sub B (by decide)⟩)
  · intro l
    rw [show 4 * (8 - (n - 1)) = 4 * m + 1 + 1 + 1 + 1 by omega_using [hn, hm', hn8], st_succ, st_succ, st_succ,
      st_succ, hst l, hx7, hx6, hx5, hx4]
    rfl
  · rw [xe, show 4 * (8 - (n - 1)) = 4 * m + 3 + 1 by omega_using [hn, hm', hn8]]
    exact c₄ _ (k₃ (4 * m + 3 + 1) (by omega_using [h1, hn, hm', hn8]))

/-- The eight turns: the four words after the 32 rounds, in the ring. -/
theorem loop_wp (hs : ScrIn s₀ B 182) {b : Nat → Spec.Sm4.Block} {n : Nat} (hn : 1 ≤ n) (hI : Inv s₀ B rk b n s) :
    WP isa (.loop (.block turn) .ne) s (Inv s₀ B rk b 0) := by
  refine WP.loop (M := isa) (fun n s => 1 ≤ n ∧ Inv s₀ B rk b n s) ?_ n s ⟨hn, hI⟩
  rintro n s ⟨hn, hI⟩
  refine WP.mono (turn_wp hs hn hI) fun s₁ ⟨z₁, i₁⟩ => ?_
  by_cases h1 : n = 1
  · subst h1
    exact .inl ⟨by show s₁.zf.map _ = _; rw [z₁]; rfl, i₁⟩
  · exact .inr ⟨by show s₁.zf.map _ = _; rw [z₁, decide_eq_false h1]; rfl, n - 1, by omega_using [hn],
      by omega_using [hn, h1], i₁⟩

/-- The last four words to the four blocks, at byte 624 of the scratch
buffer. -/
theorem cryptTail_wp {n : Nat} (hs : ScrIn s₀ B 182) (h : At s₀ B n s) (hm : ∀ q < 16, byte (s.xmm m0) q = 0x0f#8)
    {x : Nat → Nat → Word} (hw : ∀ w < 4, WordAt s.mem B w (x w)) :
    WP isa (.block cryptTail) s fun s' => s'.gpr Impl.Modes.X86.sb = B ∧ s'.gpr .esp = s₀.gpr .esp ∧
      s'.rd = s₀.rd ∧ s'.wr = s₀.wr ∧ s'.syms = s₀.syms ∧
      Frame [⟨B.setWidth 64 + BitVec.ofNat 64 624, 64⟩] s.mem s'.mem ∧
      ∀ l < 4, ∀ q < 16, sAt s'.mem B (624 + 16 * l + q) = byteAt (x (3 - q / 4) l) (q % 4) := by
  have hf : B.toNat + 728 ≤ 2 ^ 32 := hs.fit
  have he := h.env hs hm
  have hok := conv_all.2
  unfold tailOk at hok
  split at hok <;> [cases hok; rename_i ρ hrun]
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hok
  obtain ⟨⟨⟨⟨h0, h3⟩, h4⟩, h1⟩, c2⟩ := hok
  refine WP.block_append_iff.mpr (run_wp he.rel hrun fun s₁ hr hsame => ?_)
  have ev : ∀ l < 4, ∀ q < 16, (tw l q).eval (envOf params s) = byteAt (x (3 - q / 4) l) (q % 4) :=
    fun l hl q hq => by
    have hlt : oR + 16 * (3 - q / 4) + 4 * l + q % 4 < 96 := by
      show 32 + 16 * (3 - q / 4) + 4 * l + q % 4 < 96; omega_using [hl]
    have e : kb s (oR + 16 * (3 - q / 4) + 4 * l + q % 4) = wl (x (3 - q / 4) l) (q % 4) := by
      rw [h.scr]
      have := hw (3 - q / 4) (by omega_arith) (4 * l + q % 4) (by omega_using [hl])
      rw [show (4 * l + q % 4) / 4 = l by omega_arith] at this
      rw [show oR + 16 * (3 - q / 4) + 4 * l + q % 4 = 32 + 16 * (3 - q / 4) + (4 * l + q % 4) by
        show 32 + _ + _ + _ = _; omega_arith, this, wl, wl,
        show (4 * l + q % 4) % 4 = q % 4 % 4 by omega_arith]
    rw [tw, BV.eval, mask_zero, cterms_sum, BitVec.zero_xor, BitVec.xor_zero, env_key hlt, e, wl, Nat.mod_mod]
    exact pv_pl _
  have cq := fun q (hq : q < 16) => List.all_eq_true.mp c2 q (List.mem_range.mpr hq)
  simp only [Bool.and_eq_true] at cq
  have b0 : ∀ q < 16, byte (s₁.xmm .xmm0) q = byteAt (x (3 - q / 4) 0) (q % 4) := fun q hq => by
    rw [hr.bytes h0 q hq, BV.same_eval _ (cq q hq).1.1.1, ev 0 (by decide) q hq]
  have b1 : ∀ q < 16, byte (s₁.xmm .xmm3) q = byteAt (x (3 - q / 4) 1) (q % 4) := fun q hq => by
    rw [hr.bytes h3 q hq, BV.same_eval _ (cq q hq).1.1.2, ev 1 (by decide) q hq]
  have b2 : ∀ q < 16, byte (s₁.xmm .xmm4) q = byteAt (x (3 - q / 4) 2) (q % 4) := fun q hq => by
    rw [hr.bytes h4 q hq, BV.same_eval _ (cq q hq).1.2, ev 2 (by decide) q hq]
  have b3 : ∀ q < 16, byte (s₁.xmm .xmm1) q = byteAt (x (3 - q / 4) 3) (q % 4) := fun q hq => by
    rw [hr.bytes h1 q hq, BV.same_eval _ (cq q hq).2, ev 3 (by decide) q hq]
  obtain ⟨f, rfl⟩ := hsame
  refine WP.mono (stores_wp (s := { s with xmm := f }) (B := B) (o := oB) h.base
    (by show _ ∈ s.wr; rw [h.wr]; exact hs.wr) hf (by decide))
    fun s₂ ⟨g₂, _, _, rd₂, wr₂, sy₂, f₂, v0, v1, v2, v3⟩ => ?_
  refine ⟨by rw [g₂]; exact h.base, by rw [g₂]; exact h.esp, rd₂.trans h.rd, wr₂.trans h.wr, sy₂.trans h.syms,
    f₂, fun l hl q hq => ?_⟩
  rcases (show l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3 by omega_using [hl]) with rfl | rfl | rfl | rfl
  · exact (v0 q hq).trans (b0 q hq)
  · exact (v1 q hq).trans (b1 q hq)
  · exact (v2 q hq).trans (b2 q hq)
  · exact (v3 q hq).trans (b3 q hq)

/-- Block `l` of the scratch buffer's four. -/
abbrev blkAt (m : Mem) (B : BitVec 32) (l : Nat) : Spec.Sm4.Block :=
  Spec.Sm4.blockAt m (B.setWidth 64 + BitVec.ofNat 64 (624 + 16 * l))

/-- `crypt` enciphers the four blocks at byte 624 of the scratch buffer,
under the round keys in their places, and changes nothing else but the
ring. -/
theorem crypt_wp (hB : s.gpr Impl.Modes.X86.sb = B) (hs : ScrIn s B 182)
    (htab : s.mem.readW (B.setWidth 64) 32 = s.syms tableName) (hk : ∀ i < 32, KeyAt s.mem B i (rk i)) :
    WP isa crypt s fun s' => s'.gpr Impl.Modes.X86.sb = B ∧ s'.gpr .esp = s.gpr .esp ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ s'.syms = s.syms ∧
      Frame [⟨B.setWidth 64 + BitVec.ofNat 64 624, 64⟩, ⟨B.setWidth 64 + BitVec.ofNat 64 32, 64⟩] s.mem s'.mem ∧
      (∀ i < 32, KeyAt s'.mem B i (rk i)) ∧
      ∀ l < 4, Spec.Aes.bytesAt s'.mem (B.setWidth 64 + BitVec.ofNat 64 (624 + 16 * l)) 16 =
        (Spec.Sm4.crypt rk (blkAt s.mem B l)).toList := by
  show WP isa (.seq (.block cryptHead) (.seq (.loop (.block turn) .ne) (.block cryptTail))) s _
  refine WP.seq (WP.mono (cryptHead_wp hB hs htab hk) fun s₁ ⟨a₁, m₁, c₁, f₁, k₁, w₁, x₁, y₁⟩ => ?_)
  have hI : Inv s B rk (blkAt s.mem B) 8 s₁ :=
    ⟨Nat.le_refl _, a₁, m₁, c₁, f₁, k₁, bwd s.mem B 0, bwd s.mem B 1, bwd s.mem B 2, bwd s.mem B 3, fun _ => rfl,
      w₁ 0 (by decide), w₁ 1 (by decide), w₁ 2 (by decide), w₁ 3 (by decide), x₁, fun _ => y₁⟩
  refine WP.seq (WP.mono (loop_wp hs (by decide) hI)
    fun s₂ ⟨_, a₂, m₂, _, f₂, k₂, x0, x1, x2, x3, h32, v0, v1, v2, v3, _, _⟩ => ?_)
  have hw : ∀ w < 4, WordAt s₂.mem B w (fun l => [x0 l, x1 l, x2 l, x3 l].getD w 0) := fun w hw4 => by
    rcases (show w = 0 ∨ w = 1 ∨ w = 2 ∨ w = 3 by omega_using [hw4]) with rfl | rfl | rfl | rfl
    · exact v0
    · exact v1
    · exact v2
    · exact v3
  refine WP.mono (cryptTail_wp hs a₂ m₂ (x := fun w l => [x0 l, x1 l, x2 l, x3 l].getD w 0) hw)
    fun s₃ ⟨b₃, e₃, r₃, w₃, y₃, f₃, v₃⟩ => ⟨b₃, e₃, r₃, w₃, y₃, ?_, ?_, ?_⟩
  · exact (f₂.mono fun r hr => List.mem_cons_of_mem _ hr).trans (f₃.mono fun r hr => by
      rw [List.mem_singleton.mp hr]; exact List.mem_cons_self)
  · intro i hi q hq
    have := f₃.bytes (R := ⟨B.setWidth 64 + BitVec.ofNat 64 (96 + 16 * i + q), 1⟩) (fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact Offset.disjoint _ (.inl (by omega_using [hi, hq])) (by omega_using [hi, hq]) (by decide))
      (show (1 : Nat) ≤ 2 ^ 64 by decide) (i := 0) (show (0 : Nat) < 1 by decide)
    rw [BitVec.add_zero] at this
    rw [sAt, this]
    exact k₂ i hi q hq
  · intro l hl
    have hc : Spec.Sm4.crypt rk (blkAt s.mem B l) = Vector.ofFn fun i : Fin 16 =>
        byteAt ((#v[x3 l, x2 l, x1 l, x0 l] : Vector Word 4).getD (i.val / 4) 0) (i.val % 4) := by
      unfold Spec.Sm4.crypt
      rw [show (List.range 32).foldl (fun s i => Spec.Sm4.round (rk i) s) (Spec.Sm4.initial (blkAt s.mem B l)) =
          st rk (blkAt s.mem B l) 32 from rfl, show st rk (blkAt s.mem B l) 32 = (x0 l, x1 l, x2 l, x3 l) from h32 l]
      rfl
    rw [hc]
    refine List.ext_getElem (by simp [Spec.Aes.bytesAt]) fun q h₁ _ => ?_
    have hq : q < 16 := by simpa [Spec.Aes.bytesAt] using h₁
    rw [Vector.getElem_toList, Vector.getElem_ofFn]
    simp only [Spec.Aes.bytesAt, List.getElem_map, List.getElem_range]
    have := v₃ l hl q hq
    rw [sAt, ← Offset.add_ofNat_add_ofNat] at this
    rw [this]
    rcases (show q / 4 = 0 ∨ q / 4 = 1 ∨ q / 4 = 2 ∨ q / 4 = 3 by omega_using [hq]) with h | h | h | h <;> rw [h] <;> rfl

end

/-! ## The round keys `prepare` leaves -/

section

open VG.Impl.Modes.X86 (at_ argOp)

/-- The place of the schedule's round key `i`: its own, or, for decryption,
the reverse. -/
def pos : Dir → Nat → Nat
  | .encrypt, i => i
  | .decrypt, i => 31 - i

/-- The keys' pointer after `i` groups, from the scratch buffer's address. -/
def kpo : Dir → Nat → Nat
  | .encrypt, i => 96 + 64 * i
  | .decrypt, i => 544 - 64 * i

theorem pos_pos (d : Dir) {i : Nat} (hi : i < 32) : pos d (pos d i) = i := by
  cases d <;> simp only [pos] <;> omega_using [hi]

theorem pos_lt (d : Dir) {i : Nat} (hi : i < 32) : pos d i < 32 := by
  cases d <;> simp only [pos] <;> omega_using [hi]

theorem kpo_zero (d : Dir) : kpo d 0 = keyBase d := by cases d <;> rfl

theorem kpo_bounds (d : Dir) {i : Nat} (hi : i < 8) : 96 ≤ kpo d i ∧ kpo d i + 64 ≤ 608 := by
  cases d <;> simp only [kpo] <;> omega_using [hi]

/-- The place of the key that goes to `kr + 16 w` in group `i`. -/
theorem place_eq (d : Dir) {i w : Nat} (hi : i < 8) (hw : w < 4) :
    96 + 16 * pos d (4 * i + keyIdx d w) = kpo d i + 16 * w := by
  cases d <;> simp only [pos, keyIdx, kpo] <;> omega_using [hi, hw]

theorem keyIdx_lt (d : Dir) {w : Nat} (hw : w < 4) : keyIdx d w < 4 := by
  cases d <;> simp only [keyIdx] <;> omega_using [hw]

theorem keyIdx_keyIdx (d : Dir) {w : Nat} (hw : w < 4) : keyIdx d (keyIdx d w) = w := by
  cases d <;> simp only [keyIdx] <;> omega_using [hw]

/-- The places of the keys of the groups before group `m` are outside its
four. -/
theorem place_out (d : Dir) {m j q : Nat} (hm : m < 8) (hj : j < 4 * m) (hq : q < 16) :
    96 + 16 * pos d j + q < kpo d m ∨ kpo d m + 64 ≤ 96 + 16 * pos d j + q := by
  cases d <;> simp only [pos, kpo] <;> omega_using [hm, hj, hq]

/-- What `prepare` needs of the state it starts in: the scratch buffer, and
the schedule, apart from it. -/
structure PEnv (s₀ : State) (B p : BitVec 32) : Prop where
  scr : ScrIn s₀ B 182
  sch : (⟨p.setWidth 64, 128⟩ : Region) ∈ s₀.rd ++ s₀.wr
  pfit : p.toNat + 128 ≤ 2 ^ 32
  sep : Region.Disjoint ⟨p.setWidth 64, 128⟩ ⟨B.setWidth 64, 728⟩

/-- A state of `prepare d` after `i` groups of four round keys: the
schedule's pointer, the round keys' pointer, the table's address, and the
mask. -/
structure PAt (d : Dir) (s₀ : State) (B p : BitVec 32) (i : Nat) (s : State) : Prop where
  base : s.gpr Impl.Modes.X86.sb = B
  esp : s.gpr .esp = s₀.gpr .esp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  syms : s.syms = s₀.syms
  tb : s.gpr tbr = s₀.syms tableName
  sp : s.gpr .eax = p + BitVec.ofNat 32 (16 * i)
  kp : s.gpr kr = B + BitVec.ofNat 32 (kpo d i)
  msk : ∀ q < 16, byte (s.xmm m0) q = 0x0f#8

variable {d : Dir} {s₀ s : State} {B p : BitVec 32} {i : Nat} {M : Mem}

theorem PAt.kr64 (h : PAt d s₀ B p i s) (he : PEnv s₀ B p) (hi : i < 8) :
    (s.gpr kr).setWidth 64 = B.setWidth 64 + BitVec.ofNat 64 (kpo d i) := by
  have hf := he.scr.fit
  have hb := kpo_bounds d hi
  rw [h.kp]; exact addr_eq (by omega_arith)

theorem PAt.krNat (h : PAt d s₀ B p i s) (he : PEnv s₀ B p) (hi : i < 8) :
    (s.gpr kr).toNat = B.toNat + kpo d i := by
  have hf := he.scr.fit
  have hb := kpo_bounds d hi
  rw [h.kp, Offset.toNat_add_ofNat, Nat.mod_eq_of_lt (a := kpo d i) (by omega_arith),
    Nat.mod_eq_of_lt (by omega_arith)]

theorem PAt.ax64 (h : PAt d s₀ B p i s) (he : PEnv s₀ B p) (hi : i < 8) :
    (s.gpr .eax).setWidth 64 = p.setWidth 64 + BitVec.ofNat 64 (16 * i) := by
  have hf := he.pfit
  rw [h.sp]; exact addr_eq (by omega_arith)

theorem PAt.axNat (h : PAt d s₀ B p i s) (he : PEnv s₀ B p) (hi : i < 8) :
    (s.gpr .eax).toNat = p.toNat + 16 * i := by
  have hf := he.pfit
  rw [h.sp, Offset.toNat_add_ofNat, Nat.mod_eq_of_lt (a := 16 * i) (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]

theorem prepGroupOk_all (d : Dir) : prepGroupOk d = true := by
  cases d
  · exact prep_all.1
  · exact prep_all.2.1

/-- Four round keys of the schedule to their places (`prepGroupX d`). -/
theorem prepGroupX_wp (he : PEnv s₀ B p) (hi : i < 8) (h : PAt d s₀ B p i s) (hS : Sch M s.mem p) :
    WP isa (.block (prepGroupX d)) s fun s' => PAt d s₀ B p i s' ∧ s'.gpr .ecx = s.gpr .ecx ∧
      Frame [⟨B.setWidth 64 + BitVec.ofNat 64 (kpo d i), 64⟩] s.mem s'.mem ∧
      ∀ u < 4, KeyAt s'.mem B (pos d (4 * i + u)) (rkAt M p (4 * i + u)) := by
  have hf := he.scr.fit
  have hpf := he.pfit
  have hk := h.krNat he hi
  have ha := h.axNat he hi
  have hb := kpo_bounds d hi
  have rel : Rel pparams (envOf pparams s) regs₀ s :=
    (rel_init (p := pparams) (by show s.gpr tbr = s.syms tableName; rw [h.tb, h.syms])
      (by show (s.gpr .eax).toNat + 16 ≤ _; omega_arith)
      fun o ho => ⟨_, by rw [h.rd, h.wr]; exact he.sch, by
        show Region.Contains _ (addr (s.gpr .eax) o) 16
        have ho' : o + 16 ≤ 16 := ho
        rw [addr_eq (by omega_arith), h.ax64 he hi, Offset.add_ofNat_add_ofNat]
        exact Offset.contains_base _ (by omega_arith) (by omega_arith)⟩).const m0 h.msk
  have ok : OutOk pparams poparams s := by
    refine ⟨by show (s.gpr kr).toNat + 64 ≤ _; omega_arith, fun o ho => ⟨_, by rw [h.wr]; exact he.scr.wr, ?_⟩, ?_,
      by show (s.gpr .eax).toNat + 16 ≤ _; omega_arith⟩
    · show Region.Contains _ (addr (s.gpr kr) o) 16
      have ho' : o + 16 ≤ 64 := ho
      rw [addr_eq (by omega_arith), h.kr64 he hi, Offset.add_ofNat_add_ofNat]
      exact Offset.contains_base _ (by omega_arith) (by omega_arith)
    · show Region.Disjoint ⟨(s.gpr .eax).setWidth 64, 16⟩ ⟨(s.gpr kr).setWidth 64, 64⟩
      rw [h.ax64 he hi, h.kr64 he hi]
      exact (he.sep.sub_left (Offset.sub_base _ (by omega_arith))).sub_right (Offset.sub_base _ (by omega_arith))
  have hok := prepGroupOk_all d
  unfold prepGroupOk at hok
  split at hok <;> [cases hok; rename_i σ hrun]
  simp only [Bool.and_eq_true] at hok
  obtain ⟨⟨⟨⟨⟨o0, o1⟩, o2⟩, o3⟩, oin⟩, cm⟩ := hok
  refine runS_wp ok (RelS.init rel rfl) hrun fun s' hr => ?_
  simp only [maskOk, Bool.and_eq_true, Bool.not_eq_true'] at cm
  have st : ∀ {w : Nat}, outOk σ.2 (16 * w) (pw d w) = true → w < 4 →
      KeyAt s'.mem B (pos d (4 * i + keyIdx d w)) (rkAt M p (4 * i + keyIdx d w)) := fun {w} ho hw4 q hq => by
    have h4 : q % 4 < 4 := Nat.mod_lt _ (by decide)
    have hu := keyIdx_lt d hw4
    have := hr.out ho hq
    rw [show (s.gpr poparams.oreg) = s.gpr kr from rfl, h.kr64 he hi, Offset.add_ofNat_add_ofNat] at this
    rw [sAt, show 96 + 16 * pos d (4 * i + keyIdx d w) + q = kpo d i + (16 * w + q) by
        rw [place_eq d hi hw4, Nat.add_assoc], this, pw, BV.eval, mask_zero,
      cterms_sum, BitVec.zero_xor, BitVec.xor_zero, kv,
      mask_bit _ (by show 128 + (4 * keyIdx d w + (3 - q % 4)) < 1024; omega_using [hu]), envOf_key,
      show (s.gpr pparams.kreg) = s.gpr .eax from rfl, h.ax64 he hi, Offset.add_ofNat_add_ofNat,
      hS _ (by omega_using [hi, hu]), wk, byteAt_rkAt _ _ (by omega_using [hi, hu]) h4]
    rw [show 16 * i + (4 * keyIdx d w + (3 - q % 4)) = 4 * (4 * i + keyIdx d w) + (3 - q % 4) by omega_arith]
    rfl
  refine ⟨⟨by rw [hr.gpr]; exact h.base, by rw [hr.gpr]; exact h.esp, hr.rd.trans h.rd, hr.wr.trans h.wr,
    hr.syms.trans h.syms, by rw [hr.gpr]; exact h.tb, by rw [hr.gpr]; exact h.sp, by rw [hr.gpr]; exact h.kp,
    fun q hq => by
      rw [hr.rel.bytes cm.1 q hq, BV.same_eval _ (List.all_eq_true.mp cm.2 q (List.mem_range.mpr hq)), BV.cst_eval]⟩,
    by rw [hr.gpr], ?_, fun u hu => ?_⟩
  · have := hr.frameIn oin
    rw [show (s.gpr poparams.oreg) = s.gpr kr from rfl, h.kr64 he hi, Offset.add_ofNat_add_ofNat, Nat.add_zero,
      Nat.sub_zero] at this
    exact this
  · have hw := keyIdx_lt d hu
    have e := keyIdx_keyIdx d hu
    rcases (show keyIdx d u = 0 ∨ keyIdx d u = 1 ∨ keyIdx d u = 2 ∨ keyIdx d u = 3 by omega_using [hw]) with
      h0 | h0 | h0 | h0
    · have := st (w := 0) o0 (by decide); rwa [← h0, e] at this
    · have := st (w := 1) o1 (by decide); rwa [← h0, e] at this
    · have := st (w := 2) o2 (by decide); rwa [← h0, e] at this
    · have := st (w := 3) o3 (by decide); rwa [← h0, e] at this

/-- The schedule is outside what `prepare` writes. -/
theorem sch_frame {m m' : Mem} {a n : Nat} (h : Sch M m p) (he : PEnv s₀ B p)
    (hf : Frame [⟨B.setWidth 64 + BitVec.ofNat 64 a, n⟩] m m') (han : a + n ≤ 728) : Sch M m' p := fun o ho => by
  rw [← h o ho]
  refine hf.bytes (R := ⟨p.setWidth 64, 128⟩) (fun r hr => ?_) (by show (128 : Nat) ≤ 2 ^ 64; decide) ho
  rw [List.mem_singleton] at hr; subst hr
  exact he.sep.sub_right (Offset.sub_base _ han)

/-- `keyStep d`, the keys' pointer on by four places in `d`'s order. -/
theorem keyStep_wp {is : List Instr} {Q : State → Prop}
    (k : ∀ s', (∀ r, r ≠ kr → s'.gpr r = s.gpr r) → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr →
      s'.syms = s.syms → s'.xmm = s.xmm → (i < 8 → s.gpr kr = B + BitVec.ofNat 32 (kpo d i) →
      s'.gpr kr = B + BitVec.ofNat 32 (kpo d (i + 1))) → WP isa (.block is) s' Q) :
    WP isa (.block (keyStep d :: is)) s Q := by
  cases d
  · refine wp_addi_x fun s' u x => k s' u.other u.mem u.rd u.wr u.syms x fun _ hk => ?_
    rw [u.gpr, hk, show (64 : BitVec 32) = BitVec.ofNat 32 64 from rfl, Offset.add_ofNat_add_ofNat]
    rfl
  · refine wp_subi_x fun s' u x _ => k s' u.other u.mem u.rd u.wr u.syms x fun hi hk => ?_
    rw [u.gpr, hk, show kpo .decrypt i = kpo .decrypt (i + 1) + 64 by
        show 544 - 64 * i = 544 - 64 * (i + 1) + 64; omega_using [hi],
      BitVec.ofNat_add, ← BitVec.add_assoc]
    exact BitVec.add_sub_cancel _ _

/-- The loop's invariant, with `n` groups left, from the memory `m₁`. -/
def PInv (d : Dir) (s₀ : State) (M m₁ : Mem) (B p : BitVec 32) (n : Nat) (s : State) : Prop :=
  n ≤ 8 ∧ PAt d s₀ B p (8 - n) s ∧ s.gpr .ecx = BitVec.ofNat 32 n ∧ Sch M s.mem p ∧
    Frame [⟨B.setWidth 64 + BitVec.ofNat 64 96, 512⟩] m₁ s.mem ∧
    ∀ j < 4 * (8 - n), KeyAt s.mem B (pos d j) (rkAt M p j)

theorem pturn_wp {m₁ : Mem} (he : PEnv s₀ B p) {n : Nat} (hn : 1 ≤ n) (hI : PInv d s₀ M m₁ B p n s) :
    WP isa (.block (prepGroup d)) s fun s' => s'.zf = some (decide (n = 1)) ∧ PInv d s₀ M m₁ B p (n - 1) s' := by
  obtain ⟨hn8, a, hc, hS, hF, K⟩ := hI
  obtain ⟨m, hm'⟩ : ∃ m, m = 8 - n := ⟨_, rfl⟩
  rw [← hm'] at a K
  have hm8 : m < 8 := by omega_using [hn, hm']
  have hf := he.scr.fit
  have hb := kpo_bounds d hm8
  refine WP.block_append_iff.mpr (WP.mono (prepGroupX_wp he hm8 a hS) fun s₁ ⟨a₁, c₁, f₁, k₁⟩ => ?_)
  show WP isa (.block [.alu .add .eax (.imm 16), keyStep d, .alu .sub .ecx (.imm 1)]) s₁ _
  refine wp_addi_x fun s₂ u₂ x₂ => keyStep_wp (i := m) (B := B) fun s₃ o₃ m₃ rd₃ wr₃ sy₃ x₃ kp₃ =>
    wp_subi_x fun s₄ u₄ x₄ z₄ => WP.block_nil ?_
  have e₄ : s₄.mem = s₁.mem := by rw [u₄.mem, m₃, u₂.mem]
  have c₃ : s₃.gpr .ecx = BitVec.ofNat 32 n := by rw [o₃ _ (by decide), u₂.other _ (by decide), c₁, hc]
  refine ⟨?_, by omega_using [hn8], ?_, ?_, ?_, ?_, fun j hj => ?_⟩
  · rw [z₄, c₃, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, Wp.sub_beq (by omega_using [hn8]) (by decide)]
  · rw [show 8 - (n - 1) = m + 1 by omega_using [hn, hm', hn8]]
    refine ⟨?_, ?_, by rw [u₄.rd, rd₃, u₂.rd]; exact a₁.rd, by rw [u₄.wr, wr₃, u₂.wr]; exact a₁.wr,
      by rw [u₄.syms, sy₃, u₂.syms]; exact a₁.syms, ?_, ?_, ?_, by rw [x₄, x₃, x₂]; exact a₁.msk⟩
    · rw [u₄.other _ (by decide), o₃ _ (by decide), u₂.other _ (by decide)]; exact a₁.base
    · rw [u₄.other _ (by decide), o₃ _ (by decide), u₂.other _ (by decide)]; exact a₁.esp
    · rw [u₄.other _ (by decide), o₃ _ (by decide), u₂.other _ (by decide)]; exact a₁.tb
    · rw [u₄.other _ (by decide), o₃ _ (by decide), u₂.gpr, a₁.sp,
        show (16 : BitVec 32) = BitVec.ofNat 32 16 from rfl, Offset.add_ofNat_add_ofNat]
      congr 2
    · rw [u₄.other _ (by decide)]
      exact kp₃ hm8 (by rw [u₂.other _ (by decide)]; exact a₁.kp)
  · rw [u₄.gpr, c₃]; exact Wp.ofNat_pred hn
  · rw [e₄]
    exact sch_frame hS he f₁ (by omega_arith)
  · rw [e₄]
    refine hF.trans (f₁.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)
    rw [List.mem_singleton.mp hr]
    exact Offset.sub _ (by omega_arith) (by omega_arith)
  · rw [e₄]
    by_cases hj' : j < 4 * m
    · intro q hq
      have ho := place_out d hm8 hj' hq
      have hp := pos_lt d (show j < 32 by omega_using [hj', hm8])
      have := f₁.bytes (R := ⟨B.setWidth 64 + BitVec.ofNat 64 (96 + 16 * pos d j + q), 1⟩) (fun r hr => by
        rw [List.mem_singleton.mp hr]
        exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith))
        (show (1 : Nat) ≤ 2 ^ 64 by decide) (i := 0) (show (0 : Nat) < 1 by decide)
      rw [BitVec.add_zero] at this
      rw [sAt, this]
      exact K j hj' q hq
    · have := k₁ (j - 4 * m) (by omega_using [hj, hj', hn, hm', hn8])
      rwa [show 4 * m + (j - 4 * m) = j by omega_using [hj']] at this

/-- The eight groups: the 32 round keys in their places. -/
theorem ploop_wp {m₁ : Mem} (he : PEnv s₀ B p) {n : Nat} (hn : 1 ≤ n) (hI : PInv d s₀ M m₁ B p n s) :
    WP isa (.loop (.block (prepGroup d)) .ne) s (PInv d s₀ M m₁ B p 0) := by
  refine WP.loop (M := isa) (fun n s => 1 ≤ n ∧ PInv d s₀ M m₁ B p n s) ?_ n s ⟨hn, hI⟩
  rintro n s ⟨hn, hI⟩
  refine WP.mono (pturn_wp he hn hI) fun s₁ ⟨z₁, i₁⟩ => ?_
  by_cases h1 : n = 1
  · subst h1
    exact .inl ⟨by show s₁.zf.map _ = _; rw [z₁]; rfl, i₁⟩
  · exact .inr ⟨by show s₁.zf.map _ = _; rw [z₁, decide_eq_false h1]; rfl, n - 1, by omega_using [hn],
      by omega_using [hn, h1], i₁⟩

/-- The table's address to the scratch buffer's first slot, the registers
of the loop, and the mask (`prepHead d`), with the table's address in
`eax`. -/
theorem prepHead_wp (hB : s.gpr Impl.Modes.X86.sb = B) (he : PEnv s B p) (hax : s.gpr .eax = s.syms tableName)
    (hS : Sch M s.mem p) (hin0 : InRegions (s.rd ++ s.wr) (s.ea (argOp 0)) 4)
    (hp : s.mem.readW (s.ea (argOp 0)) 32 = p)
    (h0B : Region.Disjoint ⟨s.ea (argOp 0), 4⟩ ⟨B.setWidth 64, 728⟩) :
    WP isa (.block (prepHead d)) s fun s' => PAt d s B p 0 s' ∧ s'.gpr .ecx = BitVec.ofNat 32 8 ∧ Sch M s'.mem p ∧
      Frame [⟨B.setWidth 64, 4⟩] s.mem s'.mem ∧ s'.mem.readW (B.setWidth 64) 32 = s.syms tableName := by
  have hf := he.scr.fit
  have hpf := he.pfit
  have ha0 : addr B 0 = B.setWidth 64 := by rw [addr_eq (by omega_arith), BitVec.add_zero]
  have hw : InRegions s.wr (addr B 0) 4 := ⟨_, he.scr.wr, by
    rw [addr_eq (by omega_arith)]; exact Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  show WP isa (.block (.store ⟨Impl.Modes.X86.sb, 0⟩ .eax :: .mov tbr (.reg .eax) ::
    .mov .eax (.mem ⟨.esp, 4 + 4 * 0⟩) :: .mov kr (.reg Impl.Modes.X86.sb) ::
    .alu .add kr (.imm (BitVec.ofNat 32 (keyBase d))) :: .mov .ecx (.imm 8) :: [tb m0 oM0])) s _
  refine Wp.wp_stm hB hw fun s₂ u₂ => ?_
  have f₂ : Frame [⟨B.setWidth 64, 4⟩] s.mem s₂.mem := by
    rw [u₂.mem, ha0]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ 4)
  have sub4 : Region.Sub ⟨B.setWidth 64, 4⟩ ⟨B.setWidth 64, 728⟩ := Region.sub_prefix (by decide)
  have e0 : s₂.mem.readW (s.ea (argOp 0)) 32 = p := by
    rw [f₂.readW (Region.contains_self _ 4) (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact h0B.sub_right sub4) (by decide), hp]
  refine Wp.wp_mov fun s₃ u₃ => ?_
  refine Wp.wp_ldm (B := s.gpr .esp) (by rw [u₃.other _ (by decide), u₂.gpr]) (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr]; exact hin0)
    fun s₄ u₄ => ?_
  refine Wp.wp_mov fun s₅ u₅ => ?_
  refine Wp.wp_addi fun s₆ u₆ => ?_
  refine Wp.wp_movi fun s₇ u₇ => ?_
  have m₇ : s₇.mem = s₂.mem := by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem]
  have r₇ : s₇.rd = s.rd := by rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd]
  have w₇ : s₇.wr = s.wr := by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr]
  have y₇ : s₇.syms = s.syms := by rw [u₇.syms, u₆.syms, u₅.syms, u₄.syms, u₃.syms, u₂.syms]
  have b₇ : s₇.gpr Impl.Modes.X86.sb = B := by
    rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.gpr, hB]
  have sp₇ : s₇.gpr .esp = s.gpr .esp := by
    rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.gpr]
  have t₇ : s₇.gpr tbr = s.syms tableName := by
    rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr,
      u₂.gpr, hax]
  have a₇ : s₇.gpr .eax = p := by
    rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.mem]
    exact e0
  have c₇ : s₇.gpr .ecx = BitVec.ofNat 32 8 := by rw [u₇.gpr]; rfl
  have k₇ : s₇.gpr kr = B + BitVec.ofNat 32 (kpo d 0) := by
    rw [u₇.other _ (by decide), u₆.gpr, u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, hB, kpo_zero]
  have hS₇ : Sch M s₇.mem p := by
    rw [m₇]
    exact sch_frame (a := 0) hS he (by rw [BitVec.add_zero]; exact f₂) (by decide)
  have hok := prep_all.2.2
  unfold prepMaskOk at hok
  split at hok <;> [cases hok; rename_i ρ hrun]
  have hrel : Rel pparams (envOf pparams s₇) Regs.init s₇ := rel_init (p := pparams)
    (by show s₇.gpr tbr = s₇.syms tableName; rw [t₇, y₇]) (by show (s₇.gpr .eax).toNat + 16 ≤ _; rw [a₇]; omega_arith)
    fun o ho => ⟨_, by rw [r₇, w₇]; exact he.sch, by
      show Region.Contains _ (addr (s₇.gpr .eax) o) 16
      have ho' : o + 16 ≤ 16 := ho
      rw [a₇, addr_eq (by omega_arith)]
      exact Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  refine run_wp hrel hrun fun s' hr hs => ?_
  simp only [maskOk, Bool.and_eq_true, Bool.not_eq_true'] at hok
  have hm : ∀ q < 16, byte (s'.xmm m0) q = 0x0f#8 := fun q hq => by
    rw [hr.bytes hok.1 q hq, BV.same_eval _ (List.all_eq_true.mp hok.2 q (List.mem_range.mpr hq)), BV.cst_eval]
  obtain ⟨f, rfl⟩ := hs
  refine ⟨⟨b₇, sp₇, r₇, w₇, y₇, t₇, by rw [show (_ : State).gpr .eax = s₇.gpr .eax from rfl, a₇]; simp, k₇, hm⟩,
    c₇, hS₇, by rw [show (_ : State).mem = s₇.mem from rfl, m₇]; exact f₂, ?_⟩
  show s₇.mem.readW (B.setWidth 64) 32 = _
  rw [m₇, u₂.mem, ha0, Mem.readW_writeW_self32, hax]

/-- `prepare d` leaves the round keys of the schedule in their places, in
`d`'s order, and the table's address in the scratch buffer's first slot; it
writes only the core's slots before the four blocks, and the four bytes
below `esp` of the frame that gets the table's address. -/
theorem prepare_wp (d : Dir) (hB : s.gpr Impl.Modes.X86.sb = B) (he : PEnv s B p) (hesp : 4 ≤ (s.gpr .esp).toNat)
    (hin0 : InRegions (s.rd ++ s.wr) (s.ea (argOp 0)) 4) (hp : s.mem.readW (s.ea (argOp 0)) 32 = p)
    (h0B : Region.Disjoint ⟨s.ea (argOp 0), 4⟩ ⟨B.setWidth 64, 728⟩)
    (hkS : Region.Disjoint (below (s.gpr .esp) 4) ⟨p.setWidth 64, 128⟩)
    (h0S : Region.Disjoint (below (s.gpr .esp) 4) ⟨s.ea (argOp 0), 4⟩) :
    WP isa (prepare d) s fun s' => (∀ i < 32, KeyAt s'.mem B (pos d i) (rkAt s.mem p i)) ∧
      s'.mem.readW (B.setWidth 64) 32 = s.syms tableName ∧ s'.gpr Impl.Modes.X86.sb = B ∧
      s'.gpr .esp = s.gpr .esp ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.syms = s.syms ∧
      Frame [⟨B.setWidth 64, 624⟩, below (s.gpr .esp) 4] s.mem s'.mem := by
  have hf := he.scr.fit
  show WP isa (.seq (.frame (.symPush .eax tableName) (.block []) (.pop .ecx 1)) (.seq (.block (prepHead d))
    (.loop (.block (prepGroup d)) .ne))) s _
  refine WP.seq (WP.mono (symFrame_ok tableName s hesp) fun s₁ a₁ => ?_)
  have esp₁ : s₁.gpr .esp = s.gpr .esp := a₁.gpr .esp (by decide)
  have ea₁ : ∀ k, s₁.ea (argOp k) = s.ea (argOp k) := fun k => by
    show addr (s₁.gpr .esp) _ = addr (s.gpr .esp) _
    rw [esp₁]
  have he₁ : PEnv s₁ B p :=
    ⟨⟨by rw [a₁.wr]; exact he.scr.wr, he.scr.fit⟩, by rw [a₁.rd, a₁.wr]; exact he.sch, he.pfit, he.sep⟩
  have hS₁ : Sch s.mem s₁.mem p := fun o ho =>
    a₁.frame.bytes (R := ⟨p.setWidth 64, 128⟩) (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact hkS.symm) (by show (128 : Nat) ≤ 2 ^ 64; decide) ho
  have p₁ : s₁.mem.readW (s.ea (argOp 0)) 32 = p := by
    rw [a₁.frame.readW (Region.contains_self _ 4) (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact h0S.symm) (by decide), hp]
  refine WP.seq (WP.mono (prepHead_wp (d := d) (M := s.mem) (by rw [a₁.gpr _ (by decide)]; exact hB) he₁
    (by rw [a₁.addr, a₁.syms]) hS₁ (by rw [ea₁, a₁.rd, a₁.wr]; exact hin0) (by rw [ea₁]; exact p₁)
    (by rw [ea₁]; exact h0B)) fun s₂ ⟨a₂, c₂, hS₂, f₂, t₂⟩ => ?_)
  have hI : PInv d s₁ s.mem s₂.mem B p 8 s₂ :=
    ⟨Nat.le_refl _, a₂, c₂, hS₂, Frame.refl _ _, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  refine WP.mono (ploop_wp he₁ (by decide) hI) fun s₃ ⟨_, a₃, _, _, F₃, K₃⟩ => ?_
  refine ⟨K₃, ?_, a₃.base, a₃.esp.trans esp₁, a₃.rd.trans a₁.rd, a₃.wr.trans a₁.wr, a₃.syms.trans a₁.syms, ?_⟩
  · rw [F₃.readW (r := ⟨B.setWidth 64, 4⟩) (Region.contains_self _ 4) (fun r hr => by
        rw [List.mem_singleton] at hr; subst hr
        exact Offset.base_disjoint _ (by decide) (by decide)) (by decide), t₂, a₁.syms]
  · refine ((a₁.frame.mono fun r hr => ?_).trans (f₂.sub fun r hr => ?_)).trans (F₃.sub fun r hr => ?_)
    · rw [List.mem_singleton] at hr; subst hr; exact List.mem_cons_of_mem _ List.mem_cons_self
    · rw [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self, Region.sub_prefix (by decide)⟩
    · rw [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self, Offset.sub_base _ (by decide)⟩

end

/-! ## The core -/

section

open VG.Impl.Modes.X86 (at_ argOp)
open VG.Proof.Modes.X86 (coreRegion blkRegion blkAddr stkRegion slotA CoreSpec Layout)
open VG.Proof.Sm4.X86.AesNi (KeyArgs keyArgs_congr)

/-- The cipher of the direction `d`. -/
def dirCipher : Dir → Spec.Sm4.Schedule → Spec.Cbc.Cipher
  | .encrypt => Spec.Sm4.cipher
  | .decrypt => Spec.Sm4.invCipher

/-- The key `k` is ready in the scratch buffer at `B`, for the direction
`d`: its round keys in their places, in `d`'s order, and the table's
address in the first slot. -/
def Ready (d : Dir) (s : State) (B : BitVec 32) (k : Spec.Sm4.Schedule) : Prop :=
  (∀ i < 32, KeyAt s.mem B i (k.getD (pos d i) 0)) ∧ s.mem.readW (B.setWidth 64) 32 = s.syms tableName ∧
    B.toNat + 728 ≤ 2 ^ 32

theorem core_slots (d : Dir) : (core d).slots = 172 := rfl

/-- The key stays ready through what a mode writes outside the core's slots
or within its four blocks. -/
theorem ready_frame {d : Dir} {s s' : State} {B : BitVec 32} {k : Spec.Sm4.Schedule} {rs : List Region}
    (h : Ready d s B k) (hsy : s'.syms = s.syms) (hf : Frame rs s.mem s'.mem)
    (hd : ∀ r ∈ rs, Region.Disjoint (coreRegion (core d) B) r ∨ Region.Sub r (blkRegion (core d) B)) :
    Ready d s' B k := by
  obtain ⟨hk, ht, hfit⟩ := h
  have keep : ∀ {a n : Nat}, a + n ≤ 624 → ∀ r ∈ rs,
      Region.Disjoint ⟨B.setWidth 64 + BitVec.ofNat 64 a, n⟩ r := fun {a n} h₁ r hr => by
    rcases hd r hr with h | h
    · exact h.sub_left (Offset.sub_base _ (by rw [core_slots]; omega_arith))
    · exact (Offset.disjoint (B.setWidth 64) (d := a) (n := n) (e := 4 * (core d).buf)
        (k := 4 * (core d).bw * (core d).G) (by show a + n ≤ 624 ∨ 624 + 64 ≤ a; omega_arith) (by omega_arith)
        (by show 4 * 156 + 4 * 4 * 4 ≤ 2 ^ 64; decide)).sub_right h
  refine ⟨fun i hi q hq => ?_, ?_, hfit⟩
  · have := hf.bytes (R := ⟨B.setWidth 64 + BitVec.ofNat 64 (96 + 16 * i + q), 1⟩)
      (keep (by omega_arith)) (by show (1 : Nat) ≤ 2 ^ 64; decide) (i := 0) (show (0 : Nat) < 1 by decide)
    rw [BitVec.add_zero] at this
    rw [sAt, this]
    exact hk i hi q hq
  · have e := hf.readW (r := ⟨B.setWidth 64 + BitVec.ofNat 64 0, 4⟩) (a := B.setWidth 64 + BitVec.ofNat 64 0)
      (w := 32) (Region.contains_self _ 4) (keep (by decide)) (by decide)
    rw [BitVec.add_zero] at e
    rw [e, hsy]; exact ht

theorem prepare_ok {d : Dir} {s : State} {B : BitVec 32} {rs : List Region} {k : Spec.Sm4.Schedule}
    (hB : s.gpr Impl.Modes.X86.sb = B) (hs : ScrIn s B (core d).total)
    (hR : (⟨B.setWidth 64, 4 * (core d).total⟩ : Region) ∈ rs) (hk : KeyArgs s rs k)
    (hsp : (core d).stack ≤ (s.gpr .esp).toNat) :
    WP isa (core d).prepare s fun s' => Ready d s' B k ∧ s'.gpr Impl.Modes.X86.sb = B ∧
      s'.gpr .esp = s.gpr .esp ∧
      Frame [coreRegion (core d) B, stkRegion (s.gpr .esp) (core d).stack] s.mem s'.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  obtain ⟨p, hin0, hp, hk, hsch, hfit, hdis, hd0, hkS, h0S⟩ := hk
  have he : PEnv s B p := ⟨hs, hsch, hfit, hdis _ hR⟩
  refine WP.mono (prepare_wp d hB he hsp hin0 hp (hd0 _ hR) hkS h0S) fun s' ⟨K, t, b, e, rd, wr, sy, f⟩ => ?_
  refine ⟨⟨fun i hi => ?_, by rw [t, sy], hs.fit⟩, b, e, f.sub fun r hr => ?_, rd, wr⟩
  · have := K (pos d i) (pos_lt d hi)
    rw [pos_pos d hi] at this
    rw [hk]
    exact this
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self, Region.sub_prefix (by show 624 ≤ 4 * 172; decide)⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩

/-- The cipher of `d` on the 16 bytes at `p`: the rounds under the round
keys in `d`'s order. -/
theorem dirCipher_bytes (d : Dir) (k : Spec.Sm4.Schedule) (m : Mem) (p : Addr) :
    dirCipher d k (Spec.Aes.bytesAt m p 16) =
      (Spec.Sm4.crypt (fun i => k.getD (pos d i) 0) (Spec.Sm4.blockAt m p)).toList := by
  cases d
  · rw [dirCipher, Spec.Sm4.cipher, Proof.Sm4.bytesAt_eq_blockAt, Proof.Sm4.ofFn_toList]; rfl
  · rw [dirCipher, Spec.Sm4.invCipher, Proof.Sm4.bytesAt_eq_blockAt, Proof.Sm4.ofFn_toList]; rfl

theorem crypt_ok {d : Dir} {s : State} {B : BitVec 32} {k : Spec.Sm4.Schedule}
    (hB : s.gpr Impl.Modes.X86.sb = B) (hs : ScrIn s B (core d).total) (hr : Ready d s B k) :
    WP isa (core d).crypt s fun s' => s'.gpr Impl.Modes.X86.sb = B ∧ s'.gpr .esp = s.gpr .esp ∧ Ready d s' B k ∧
      Frame [coreRegion (core d) B, stkRegion (s.gpr .esp) (core d).stack] s.mem s'.mem ∧
      (∀ j < (core d).G, Spec.Aes.bytesAt s'.mem (blkAddr (core d) B j) (4 * (core d).bw) =
        dirCipher d k (Spec.Aes.bytesAt s.mem (blkAddr (core d) B j) (4 * (core d).bw))) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨hk, ht, hfit⟩ := hr
  refine WP.mono (crypt_wp hB hs ht hk) fun s' ⟨b, e, rd, wr, sy, f, k', v⟩ => ?_
  have hblk : ∀ j, blkAddr (core d) B j = B.setWidth 64 + BitVec.ofNat 64 (624 + 16 * j) := fun j => by
    show B.setWidth 64 + BitVec.ofNat 64 (4 * 156) + BitVec.ofNat 64 (4 * 4 * j) = _
    rw [Offset.add_ofNat_add_ofNat]
  refine ⟨b, e, ⟨k', ?_, hfit⟩, f.sub fun r hr => ?_, fun j hj => ?_, rd, wr⟩
  · rw [f.readW (r := ⟨B.setWidth 64, 4⟩) (Region.contains_self _ 4) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Offset.base_disjoint _ (by decide) (by decide)
      · exact Offset.base_disjoint _ (by decide) (by decide)) (by decide), sy]
    exact ht
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self, Offset.sub_base _ (by show 624 + 64 ≤ 4 * 172; decide)⟩
    · exact ⟨_, List.mem_cons_self, Offset.sub_base _ (by show 32 + 64 ≤ 4 * 172; decide)⟩
  · rw [hblk, show 4 * (core d).bw = 16 from rfl, dirCipher_bytes]
    exact v j hj

/-- SM4's core by the AES S-box for four blocks, in the direction `d`,
meets what the modes need. -/
def coreSpec (d : Dir) : CoreSpec (core d) where
  Key := Spec.Sm4.Schedule
  cipher k := dirCipher d k
  KeyArgs := KeyArgs
  Ready := Ready d
  cipher_len _ _ := by cases d <;> simp [dirCipher, Spec.Sm4.cipher, Spec.Sm4.invCipher, core]
  layout := ⟨by show 0 < 4; decide, .inr rfl, by show 156 + 4 * 4 ≤ 172; decide,
    by show 172 + 10 ≤ 172 + 10; decide⟩
  keyArgs_congr h e r w _ f := keyArgs_congr h e r w f
  ready_frame h _ _ _ sy f _ hd := ready_frame h sy f hd
  prepare_wp hB hs hR hk hsp := prepare_ok hB hs hR hk hsp
  crypt_wp hB hs hr _ := crypt_ok hB hs hr

end

end VG.Proof.Sm4.X86.AesNiWide
