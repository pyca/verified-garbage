module

public import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Stitch.Prefix
public import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.CT
import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Stitch.Lit
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# ChaCha20 and Poly1305 together (x86-64): `cryptS`

`Stitch.cryptS`, in `seal`'s context: the data encrypted as `crypt` does
(`crypt_ok`), and, of its first `a` bytes (a multiple of 16, `aOf`), the
ciphertext absorbed into the Poly1305 state; `rbx`, `rbp` are the rest of
it, for `macPadLengths`. Without whole chunks `a` is 0; with them, `bulk`
encrypts them (`bulk_ok`, moved to `seal`'s permissions with
`RegionModel.wp_narrow`) and absorbs all but the last, and
`vg_chacha20_xor` encrypts the rest from the counter `bulk` leaves
(`call_mid`), if any is left (`callIf_ok`); or, with 1 to 448 bytes left,
`bulk` encrypts those too and absorbs all the chunks (`DoneT`).
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.X86_64.Stitch

open VG VG.X86_64 VG.Impl.ChaCha20Poly1305.X86_64 VG.Impl.ChaCha20Poly1305.X86_64.Stitch
open VG.Proof.ChaCha20 (ctr)
open VG.Spec.ChaCha20 (stateAt keystream initState)
open VG.Spec.Poly1305 (Repr bytesAt)

variable {e : Bool}

theorem seq3 {a b : Prog isa} {l₁ l₂ : List Instr} {s : State} {Q : State → Prop}
    (h : WP isa (.seq a (.seq b (.block l₁))) s fun s' => WP isa (.block l₂) s' Q) :
    WP isa (.seq a (.seq b (.block (l₁ ++ l₂)))) s Q := by
  rw [WP.seq_iff] at h ⊢
  refine WP.mono h fun _ h₁ => ?_
  rw [WP.seq_iff] at h₁ ⊢
  exact WP.mono h₁ fun _ h₂ => WP.block_append_iff.mpr h₂

theorem whole_ok (s : State) :
    WP isa (.block whole) s fun s' => s'.gpr .rbx = s.gpr .r14 ∧ s'.gpr .rbp = s.gpr .r13 ∧
      (∀ r, r ≠ .rbx → r ≠ .rbp → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = s.mem := by
  apply WP.of_runBlock
  simp only [whole, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.setReg, Option.map_some,
    Option.some.injEq, exists_eq_left', ite_true, reduceCtorEq, ite_false]
  exact ⟨trivial, trivial, fun r h₁ h₂ => by simp [h₁, h₂], trivial, trivial, trivial⟩

theorem cmp512_ok {n : Nat} (hn : n < 2 ^ 64) {s : State} (hrdx : s.gpr .rdx = BitVec.ofNat 64 n) :
    WP isa (.block [.alu .cmp .rdx (.imm 512)]) s fun s' =>
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = s.mem ∧ s'.cf = some (decide (n < 512)) := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, arithFlags, State.setFlags,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, trivial, trivial, ?_⟩
  rw [hrdx, toNat_ofNat_lt hn, show BitVec.signExtend 64 (512 : BitVec 32) = BitVec.ofNat 64 512 by decide,
    toNat_ofNat_lt (by decide)]

theorem cmp513_ok {n : Nat} (hn : n < 2 ^ 64) {s : State} (hrdx : s.gpr .rdx = BitVec.ofNat 64 n) :
    WP isa (.block [.alu .cmp .rdx (.imm 513)]) s fun s' =>
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = s.mem ∧ s'.cf = some (decide (n < 513)) := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, arithFlags, State.setFlags,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, trivial, trivial, ?_⟩
  rw [hrdx, toNat_ofNat_lt hn, show BitVec.signExtend 64 (513 : BitVec 32) = BitVec.ofNat 64 513 by decide,
    toNat_ofNat_lt (by decide)]

/-- A byte of data that `bytesAt_xor` describes. -/
theorem xor_at {m m' : Mem} {p : Addr} {n : Nat} {ks : List Byte} (hks : ks.length = n)
    (h : bytesAt m' p n = List.zipWith (· ^^^ ·) (bytesAt m p n) ks) {j : Nat} (hj : j < n) :
    m' (p + BitVec.ofNat 64 j) = m (p + BitVec.ofNat 64 j) ^^^ ks.getD j 0 := by
  have := congrArg (fun l => l.getD j 0) h
  simp only [bytesAt, List.getD_eq_getElem?_getD, List.getElem?_zipWith, List.getElem?_map,
    List.getElem?_range hj, Option.map_some, Option.getD_some] at this
  rw [List.getElem?_eq_getElem (by omega)] at this
  rw [this, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
  rfl

/-- The ciphertext `cryptS` absorbs of `L` bytes, for an implementation of
`vg_chacha20_xor` with `fold` (448): none if `L ≤ fold`; all but the last 1
to 448 bytes if the prologue computed the keystream of the first `fold`
(`PreLen`, `splitM` for `pass` 512); else the whole
chunks if `tailS` or `tailK` encrypts the rest (1 to 448 bytes after at least one
chunk), or all but the last of them. -/
abbrev aOf (fold L : Nat) : Nat :=
  if L ≤ fold then 0 else
  if PreLen fold L then fold + 512 * ((L - fold - 1) / 512) else
  if 512 ≤ L ∧ 1 ≤ L % 512 ∧ L % 512 ≤ 448 then 512 * (L / 512) else 512 * (L / 512) - 512

/-- The lengths whose rest `tailS` or `tailK` encrypts: after the first `fold` bytes
(whose keystream the prologue computed) and the whole chunks, or after the
whole chunks. -/
abbrev TailLen (fold L : Nat) : Prop :=
  (fold < L ∧ PreLen fold L) ∨ (512 ≤ L ∧ 1 ≤ L % 512 ∧ L % 512 ≤ 448)

/-- After `cryptS`'s first part, before the keystream is wiped: the data
encrypted, and its first `a` bytes of ciphertext absorbed. -/
structure CryptedS (fold : Nat) (s₀ s : State) (key msg : List Byte) (s' : State) : Prop where
  rsi : s'.gpr .rsi = off (cx s₀) 128
  keep : ∀ r, r = .r12 ∨ r = .r13 ∨ r = .r14 ∨ r = .rsp → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  frame : Frame [sub s₀ 64 512, sub s₀ 736 512, dR s₀, stkR s₀] s.mem s'.mem
  data : bytesAt s'.mem (dp s₀) (L s₀) = Spec.ChaCha20.encrypt (K s₀) 1 (N s₀) (bytesAt s.mem (dp s₀) (L s₀))
  abs : ∃ a, a = aOf fold (L s₀) ∧ a % 16 = 0 ∧ a ≤ L s₀ ∧ s'.gpr .rbx = dp s₀ + BitVec.ofNat 64 a ∧
    s'.gpr .rbp = BitVec.ofNat 64 (L s₀ - a) ∧
    Repr s'.mem (off (cx s₀) 448) key (msg ++ bytesAt s'.mem (dp s₀) a)

/-- Before the call of `vg_chacha20_xor`: the first `E` bytes (a multiple of
64) encrypted, and the first `a` of them absorbed. -/
structure Mid (fold : Nat) (s₀ s : State) (key msg : List Byte) (E a : Nat) (s' : State) : Prop where
  rdi : s'.gpr .rdi = off (cx s₀) 64
  rcx : s'.gpr .rcx = off (cx s₀) 128
  rsi : s'.gpr .rsi = dp s₀ + BitVec.ofNat 64 E
  rdx : s'.gpr .rdx = BitVec.ofNat 64 (L s₀ - E)
  rbx : s'.gpr .rbx = dp s₀ + BitVec.ofNat 64 a
  rbp : s'.gpr .rbp = BitVec.ofNat 64 (L s₀ - a)
  keep : ∀ r, r = .r12 ∨ r = .r13 ∨ r = .r14 ∨ r = .rsp → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  E64 : E % 64 = 0
  Ediv : E = 512 * (L s₀ / 512)
  aEq : a = E - 512
  EL : E ≤ L s₀
  aE : a ≤ E
  a16 : a % 16 = 0
  aO : a = aOf fold (L s₀)
  st : stateAt s'.mem (off (cx s₀) 64) = ctr (initState (K s₀) 1 (N s₀)) (E / 64)
  data : ∀ k < L s₀, s'.mem (dp s₀ + BitVec.ofNat 64 k) = if k < E then
    s.mem (dp s₀ + BitVec.ofNat 64 k) ^^^ (keystream (initState (K s₀) 1 (N s₀)) (L s₀)).getD k 0
    else s.mem (dp s₀ + BitVec.ofNat 64 k)
  frame : Frame [sub s₀ 64 512, sub s₀ 736 512, dR s₀] s.mem s'.mem
  repr : Repr s'.mem (off (cx s₀) 448) key (msg ++ bytesAt s'.mem (dp s₀) a)

theorem toNat_add_le (p : Addr) (E : Nat) (hE : E < 2 ^ 64) :
    (p + BitVec.ofNat 64 E).toNat ≤ p.toNat + E := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hE]
  exact Nat.mod_le _ _

/-- The rest of the data, `[E, L)`, encrypted by the implementation `v` of
`vg_chacha20_xor`. -/
theorem call_mid (v : Proof.ChaCha20.X86_64.XorImpl) {s₀ : State} (hp : APre e s₀) {s : State} (h : Inv s₀ s)
    {key msg : List Byte} {E a : Nat} {s₃ : State} (hm : Mid v.callee.fold s₀ s key msg E a s₃) :
    WP isa (.call v.callee.name v.callee.code) s₃ (CryptedS v.callee.fold s₀ s key msg) := by
  have hL9 : L s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  have hEL := hm.EL
  have dsub : Region.Sub ⟨dp s₀ + BitVec.ofNat 64 E, L s₀ - E⟩ (dR s₀) := Offset.sub_base _ (by omega)
  have rsp₃ : s₃.gpr .rsp = s₀.gpr .rsp := by rw [hm.keep _ (.inr (.inr (.inr rfl))), h.rsp]
  have hw : Covers [⟨off (cx s₀) 64, 64⟩, ⟨dp s₀ + BitVec.ofNat 64 E, L s₀ - E⟩, ⟨off (cx s₀) 128, 320⟩]
      s₃.wr := by
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨ctxR s₀, by rw [hm.wr, h.wr]; exact hp.ctx_wr, 64, by simp [off_eq], by show 64 + 64 ≤ 1696; omega⟩
    · exact ⟨dR s₀, by rw [hm.wr, h.wr]; exact hp.d_wr, E, rfl, by show E + (L s₀ - E) ≤ L s₀; omega⟩
    · exact ⟨ctxR s₀, by rw [hm.wr, h.wr]; exact hp.ctx_wr, 128, by simp [off_eq], by show 128 + 320 ≤ 1696; omega⟩
  refine xor_call v (S := off (cx s₀) 64) (D := dp s₀ + BitVec.ofNat 64 E) (B := off (cx s₀) 128)
    hm.rdi hm.rsi hm.rdx hm.rcx (by omega)
    ((hp.c_d.sub_left (sub_ctx s₀ (k := 64) (n := 64) (by lit_omega))).sub_right dsub)
    (sub_disj s₀ (a := 64) (n := 64) (b := 128) (m := 320) (by lit_omega) (by lit_omega) (by lit_omega))
    ((hp.c_d.symm.sub_right (sub_ctx s₀ (k := 128) (n := 320) (by lit_omega))).sub_left dsub)
    (Nat.le_trans (Nat.add_le_add_right (toNat_add_le _ E (by omega)) _) (by have := hp.wrap_d; omega))
    (by rw [rsp₃]; exact hp.stk_sub (by lit_omega)) (by rw [rsp₃]; exact hp.stk_d.sub_right dsub)
    (by rw [rsp₃]; exact hp.stk_sub (by lit_omega)) (Covers.right hw) hw
    fun s' rd' wr' cs' f' rsi' data' => ?_
  rw [rsp₃] at f'
  have ks' : (keystream (stateAt s₃.mem (off (cx s₀) 64)) (L s₀ - E)).length = L s₀ - E :=
    VG.Proof.ChaCha20.length_keystream _ _
  have hd : ∀ k < E, ∀ r ∈ [⟨off (cx s₀) 64, 64⟩, ⟨dp s₀ + BitVec.ofNat 64 E, L s₀ - E⟩,
      ⟨off (cx s₀) 128, 320⟩, stkR s₀], ¬ r.Contains (dp s₀ + BitVec.ofNat 64 k) 1 := by
    intro k hk r hr hc
    have hin : (dR s₀).Contains (dp s₀ + BitVec.ofNat 64 k) 1 :=
      Offset.contains_base _ (by omega) (by omega)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hp.c_d _ (sub_ctx s₀ (k := 64) (n := 64) (by lit_omega) _ hc) hin
    · simp only [Region.Contains] at hc
      rw [Offset.sub_toNat' _ (by omega) (by omega)] at hc
      split at hc <;> omega
    · exact hp.c_d _ (sub_ctx s₀ (k := 128) (n := 320) (by lit_omega) _ hc) hin
    · exact hp.stk_d _ hc hin
  refine ⟨rsi', fun r hr => ?_, by rw [rd', hm.rd], by rw [wr', hm.wr], ?_, ?_,
    ⟨a, hm.aO, hm.a16, Nat.le_trans hm.aE hEL, by rw [cs' _ (by simp [calleeSaved]), hm.rbx],
      by rw [cs' _ (by simp [calleeSaved]), hm.rbp], ?_⟩⟩
  · rw [cs' r (by rcases hr with rfl | rfl | rfl | rfl <;> simp [calleeSaved]), hm.keep r hr]
  · refine (hm.frame.mono (by simp)).trans (f'.sub fun r hr => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨sub s₀ 64 512, by simp, sub_sub s₀ (Nat.le_refl _) (by lit_omega) (by lit_omega)⟩
    · exact ⟨dR s₀, by simp, dsub⟩
    · exact ⟨sub s₀ 64 512, by simp, sub_sub s₀ (by lit_omega) (by lit_omega) (by lit_omega)⟩
    · exact ⟨stkR s₀, by simp, fun _ h => h⟩
  · rw [encrypt_eq, VG.Proof.Poly1305.length_bytesAt]
    apply VG.Proof.ChaCha20.bytesAt_xor (VG.Proof.ChaCha20.length_keystream _ _)
    intro k hk
    by_cases hkE : k < E
    · rw [f' _ (hd k hkE), hm.data k hk, ite_eq_left hkE]
    · have x := xor_at ks' data' (j := k - E) (by omega)
      rw [Offset.add_add, Nat.add_sub_cancel' (by omega), hm.st, ks_from _ hm.E64 hk (by omega),
        hm.data k hk, ite_eq_right hkE] at x
      exact x
  · have hb : bytesAt s'.mem (dp s₀) a = bytesAt s₃.mem (dp s₀) a := by
      simp only [bytesAt]
      apply List.map_congr_left
      intro k hk
      rw [List.mem_range] at hk
      exact f' _ (hd k (by have := hm.aE; omega))
    rw [hb]
    refine Repr.frame f' (fun r hr => ?_) hm.repr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
    · exact (hp.c_d.sub_left (sub_ctx s₀ (by lit_omega))).sub_right dsub
    · exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
    · exact (hp.stk_sub (by lit_omega)).symm

/-- After `cryptArgs` (and the comparison with 512): the counter set to 1
and the arguments of `vg_chacha20_xor`. -/
structure Args (s₀ s : State) (s₂ : State) : Prop where
  mem : s₂.mem = s.mem.writeW (off (cx s₀) 112) (1 : BitVec 32)
  rdi : s₂.gpr .rdi = off (cx s₀) 64
  rsi : s₂.gpr .rsi = dp s₀
  rdx : s₂.gpr .rdx = BitVec.ofNat 64 (L s₀)
  rcx : s₂.gpr .rcx = off (cx s₀) 128
  r13 : s₂.gpr .r13 = BitVec.ofNat 64 (L s₀)
  r14 : s₂.gpr .r14 = dp s₀
  keep : ∀ r, r = .r12 ∨ r = .r13 ∨ r = .r14 ∨ r = .rsp → s₂.gpr r = s.gpr r
  rd : s₂.rd = s.rd
  wr : s₂.wr = s.wr

theorem args_frame (s₀ : State) (m : Mem) :
    Frame [sub s₀ 112 4] m (m.writeW (off (cx s₀) 112) (1 : BitVec 32)) :=
  (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (contains_sub s₀ (by lit_omega) (by lit_omega) (by lit_omega))

theorem args_data {s₀ : State} (hp : APre e s₀) (m : Mem) {k : Nat} (hk : k < L s₀) :
    (m.writeW (off (cx s₀) 112) (1 : BitVec 32)) (dp s₀ + BitVec.ofNat 64 k) = m (dp s₀ + BitVec.ofNat 64 k) :=
  args_frame s₀ m _ fun r hr hc => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.c_d _ (sub_ctx s₀ (by lit_omega) _ hc)
      (Offset.contains_base _ (by omega) (by have : L s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt; omega))

theorem args_repr {s₀ : State} {m : Mem} {key msg : List Byte} (h : Repr m (off (cx s₀) 448) key msg) :
    Repr (m.writeW (off (cx s₀) 112) (1 : BitVec 32)) (off (cx s₀) 448) key msg :=
  Repr.frame (args_frame s₀ m) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)) h

/-- No whole chunks: nothing encrypted yet, nothing absorbed. -/
theorem whole_mid {fold : Nat} {s₀ : State} (hp : APre e s₀) {s s₂ : State} (ha : Args s₀ s s₂)
    (hnp : ¬ PreLen fold (L s₀)) (hlt : L s₀ < 512)
    (hst : stateAt s.mem (off (cx s₀) 64) = initState (K s₀) 0 (N s₀))
    {key msg : List Byte} (hrep : Repr s.mem (off (cx s₀) 448) key msg) :
    WP isa (.block whole) s₂ (Mid fold s₀ s key msg 0 0) := by
  refine WP.mono (whole_ok s₂) fun s₃ ⟨rbx₃, rbp₃, g₃, rd₃, wr₃, m₃⟩ => ?_
  have z : dp s₀ + BitVec.ofNat 64 0 = dp s₀ := by simp
  refine ⟨by rw [g₃ _ (by decide) (by decide), ha.rdi], by rw [g₃ _ (by decide) (by decide), ha.rcx],
    by rw [g₃ _ (by decide) (by decide), ha.rsi, z], by rw [g₃ _ (by decide) (by decide), ha.rdx, Nat.sub_zero],
    by rw [rbx₃, ha.r14, z], by rw [rbp₃, ha.r13, Nat.sub_zero], fun r hr => ?_, by rw [rd₃, ha.rd],
    by rw [wr₃, ha.wr], rfl, by omega, rfl, Nat.zero_le _, Nat.le_refl _, rfl,
    by simp only [aOf, PreLen] at hnp ⊢; rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]; omega,
    ?_, fun k hk => ?_, ?_, ?_⟩
  · rw [g₃ r (by rcases hr with rfl | rfl | rfl | rfl <;> decide) (by rcases hr with rfl | rfl | rfl | rfl <;> decide),
      ha.keep r hr]
  · rw [m₃, ha.mem, stateAt_ctr, hst, set12_initState, Nat.zero_div, VG.Proof.ChaCha20.ctr_zero]
  · rw [m₃, ha.mem, args_data hp _ hk, ite_eq_right (Nat.not_lt_zero _)]
  · rw [m₃, ha.mem]
    exact (args_frame s₀ _).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨sub s₀ 64 512, by simp, sub_sub s₀ (by lit_omega) (by lit_omega) (by lit_omega)⟩
  · rw [show bytesAt s₃.mem (dp s₀) 0 = [] from rfl, List.append_nil, m₃, ha.mem]
    exact args_repr hrep

/-- After `bulk` ended by `tailS`: the data encrypted, its whole chunks
absorbed, and nothing left to encrypt. -/
structure DoneT (fold : Nat) (s₀ s : State) (key msg : List Byte) (s' : State) : Prop where
  rdx : s'.gpr .rdx = 0
  rcx : s'.gpr .rcx = off (cx s₀) 128
  keep : ∀ r, r = .r12 ∨ r = .r13 ∨ r = .r14 ∨ r = .rsp → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  frame : Frame [sub s₀ 64 512, sub s₀ 736 512, dR s₀] s.mem s'.mem
  data : bytesAt s'.mem (dp s₀) (L s₀) = Spec.ChaCha20.encrypt (K s₀) 1 (N s₀) (bytesAt s.mem (dp s₀) (L s₀))
  abs : ∃ a, a = aOf fold (L s₀) ∧ a % 16 = 0 ∧ a ≤ L s₀ ∧ s'.gpr .rbx = dp s₀ + BitVec.ofNat 64 a ∧
    s'.gpr .rbp = BitVec.ofNat 64 (L s₀ - a) ∧
    Repr s'.mem (off (cx s₀) 448) key (msg ++ bytesAt s'.mem (dp s₀) a)
  tail : TailLen fold (L s₀)

/-- The whole chunks: `bulk`, with its permissions. -/
theorem bulk_mid (vl : Bool) {fold : Nat} {s₀ : State} (hp : APre e s₀) {s s₂ : State} (hwr : s.wr = s₀.wr) (ha : Args s₀ s s₂)
    (hf : fold < L s₀) (hnp : ¬ PreLen fold (L s₀)) (hge : 512 ≤ L s₀)
    (hst : stateAt s.mem (off (cx s₀) 64) = initState (K s₀) 0 (N s₀))
    {key msg : List Byte} (hrep : Repr s.mem (off (cx s₀) 448) key msg) :
    WP isa (bulk vl) s₂ fun s₃ => (∃ E a, Mid fold s₀ s key msg E a s₃) ∨ DoneT fold s₀ s key msg s₃ := by
  have hL9 : L s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  have hl : Lay (cx s₀) (dp s₀) (L s₀) := ⟨hL9, hp.wrap_d, hp.c_d.sub_left (Region.sub_prefix (by decide))⟩
  have st₂ : stateAt s₂.mem (stA (cx s₀)) = initState (K s₀) 1 (N s₀) := by
    show stateAt s₂.mem (cx s₀ + BitVec.ofNat 64 64) = _
    rw [ha.mem, ← off_eq, stateAt_ctr, hst, set12_initState]
  have hw : Covers (bulkWr (cx s₀) (dp s₀) (L s₀)) s₂.wr := by
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ⟨ctxR s₀, by rw [ha.wr, hwr]; exact hp.ctx_wr, 64, rfl, by show 64 + 64 ≤ 1696; omega⟩
    · exact ⟨dR s₀, by rw [ha.wr, hwr]; exact hp.d_wr, 0, by simp, by simp⟩
    · exact ⟨ctxR s₀, by rw [ha.wr, hwr]; exact hp.ctx_wr, 128, rfl, by show 128 + 320 ≤ 1696; omega⟩
    · exact ⟨ctxR s₀, by rw [ha.wr, hwr]; exact hp.ctx_wr, 448, rfl, by show 448 + 128 ≤ 1696; omega⟩
    · exact ⟨ctxR s₀, by rw [ha.wr, hwr]; exact hp.ctx_wr, 736, by simp only [kA, bfA, Offset.add_add]; try rfl,
        by show 736 + 512 ≤ 1696; omega⟩
  have hn : (bulk vl).noCalls = true := by cases vl <;> decide +kernel
  refine regionModel.wp_narrow (r := []) (w := bulkWr (cx s₀) (dp s₀) (L s₀))
    (bulk_ok vl hl hge (s := s₂.withRegions [] (bulkWr (cx s₀) (dp s₀) (L s₀))) rfl rfl ha.rsi ha.rdx
      (by rw [State.withRegions_gpr, ha.rcx, off_eq])
      (by show Repr _ (cx s₀ + BitVec.ofNat 64 448) _ _
          rw [State.withRegions_mem, ha.mem, ← off_eq]; exact args_repr hrep))
    (Covers.right hw) hw (Code.noFrames_of_noCalls hn) (.inl hn) fun _ s₃ _ rd₃ wr₃ f₃ hP => ?_
  have f₃' : Frame (bulkWr (cx s₀) (dp s₀) (L s₀)) s₂.mem s₃.mem := f₃
  have fr : Frame [sub s₀ 64 512, sub s₀ 736 512, dR s₀] s.mem s₃.mem := by
    rw [ha.mem] at f₃'
    refine ((args_frame s₀ s.mem).sub fun r hr => ?_).trans (f₃'.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨sub s₀ 64 512, by simp, sub_sub s₀ (by lit_omega) (by lit_omega) (by lit_omega)⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      have e : sub s₀ 64 512 = ⟨cx s₀ + BitVec.ofNat 64 64, 512⟩ := by rw [sub, off_eq]
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact ⟨sub s₀ 64 512, by simp, by rw [e]; exact Offset.sub _ (by decide) (by decide)⟩
      · exact ⟨dR s₀, by simp, fun _ h => h⟩
      · exact ⟨sub s₀ 64 512, by simp, by rw [e]; exact Offset.sub _ (by decide) (by decide)⟩
      · exact ⟨sub s₀ 64 512, by simp, by rw [e]; exact Offset.sub _ (by decide) (by decide)⟩
      · exact ⟨sub s₀ 736 512, by simp, by
          rw [show kR (bfA (cx s₀)) = sub s₀ 736 512 by simp only [kR, kA, bfA, sub, off_eq, Offset.add_add]]
          exact fun _ h => h⟩
  rcases hP with ⟨T, ⟨t1, le, lt, hx, data, cnt, repr, rbx, rbp, rsi, rdx, rdi, rcx, r12, r13, r14, r15, rsp, -, -⟩ |
    ⟨t1, le, lo, hi, data, repr, rbx, rbp, rdx, rcx, r12, r13, r14, r15, rsp, -, -⟩⟩
  · -- Ended by `leave`.
    have cnt' : stateAt s₃.mem (cx s₀ + BitVec.ofNat 64 64) =
        ctr (stateAt s₂.mem (cx s₀ + BitVec.ofNat 64 64)) (8 * T) := cnt
    have data' : ∀ k < L s₀, s₃.mem (dp s₀ + BitVec.ofNat 64 k) = if k < 512 * T then
        s₂.mem (dp s₀ + BitVec.ofNat 64 k) ^^^
          (keystream (stateAt s₂.mem (cx s₀ + BitVec.ofNat 64 64)) (L s₀)).getD k 0
        else s₂.mem (dp s₀ + BitVec.ofNat 64 k) := data
    refine .inl ⟨512 * T, 512 * (T - 1), by rw [off_eq]; exact rdi, by rw [off_eq]; exact rcx, rsi, rdx, rbx, rbp,
      fun r hr => ?_, (rd₃ : s₃.rd = s₂.rd).trans ha.rd, (wr₃ : s₃.wr = s₂.wr).trans ha.wr, by omega,
      by omega, by omega, le, by omega, by omega,
      by simp only [aOf, PreLen] at hnp ⊢; rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]; omega,
      ?_, fun k hk => ?_, fr,
      by rw [off_eq]; exact repr⟩
    · rcases hr with rfl | rfl | rfl | rfl
      · exact (r12 : s₃.gpr .r12 = s₂.gpr .r12).trans (ha.keep _ (.inl rfl))
      · exact (r13 : s₃.gpr .r13 = s₂.gpr .r13).trans (ha.keep _ (.inr (.inl rfl)))
      · exact (r14 : s₃.gpr .r14 = s₂.gpr .r14).trans (ha.keep _ (.inr (.inr (.inl rfl))))
      · exact (rsp : s₃.gpr .rsp = s₂.gpr .rsp).trans (ha.keep _ (.inr (.inr (.inr rfl))))
    · rw [off_eq, cnt', st₂, show 512 * T / 64 = 8 * T by omega]
    · rw [data' k hk, st₂, ha.mem, args_data hp _ hk]
  · -- Ended by `tailS`.
    have data' : ∀ k < L s₀, s₃.mem (dp s₀ + BitVec.ofNat 64 k) = s₂.mem (dp s₀ + BitVec.ofNat 64 k) ^^^
        (keystream (stateAt s₂.mem (cx s₀ + BitVec.ofNat 64 64)) (L s₀)).getD k 0 := data
    refine .inr ⟨rdx, by rw [off_eq]; exact rcx, fun r hr => ?_, (rd₃ : s₃.rd = s₂.rd).trans ha.rd,
      (wr₃ : s₃.wr = s₂.wr).trans ha.wr, fr, ?_,
      ⟨512 * T, by simp only [aOf, PreLen] at hnp ⊢; rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega)]; omega,
        by omega, le, rbx, rbp, by rw [off_eq]; exact repr⟩, .inr (by omega)⟩
    · rcases hr with rfl | rfl | rfl | rfl
      · exact (r12 : s₃.gpr .r12 = s₂.gpr .r12).trans (ha.keep _ (.inl rfl))
      · exact (r13 : s₃.gpr .r13 = s₂.gpr .r13).trans (ha.keep _ (.inr (.inl rfl)))
      · exact (r14 : s₃.gpr .r14 = s₂.gpr .r14).trans (ha.keep _ (.inr (.inr (.inl rfl))))
      · exact (rsp : s₃.gpr .rsp = s₂.gpr .rsp).trans (ha.keep _ (.inr (.inr (.inr rfl))))
    · rw [encrypt_eq, VG.Proof.Poly1305.length_bytesAt]
      apply VG.Proof.ChaCha20.bytesAt_xor (VG.Proof.ChaCha20.length_keystream _ _)
      intro k hk
      rw [data' k hk, st₂, ha.mem, args_data hp _ hk]

/-- The permissions of the chunks are `seal`'s. -/
theorem bulk_covers' {s₀ : State} (hp : APre e s₀) : Covers (bulkWr (cx s₀) (dp s₀) (L s₀)) s₀.wr := by
  refine Covers.of_sub fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact ⟨ctxR s₀, hp.ctx_wr, 64, rfl, by show 64 + 64 ≤ 1696; omega⟩
  · exact ⟨dR s₀, hp.d_wr, 0, by simp, by simp⟩
  · exact ⟨ctxR s₀, hp.ctx_wr, 128, rfl, by show 128 + 320 ≤ 1696; omega⟩
  · exact ⟨ctxR s₀, hp.ctx_wr, 448, rfl, by show 448 + 128 ≤ 1696; omega⟩
  · exact ⟨ctxR s₀, hp.ctx_wr, 736, by simp only [kA, bfA, Offset.add_add]; try rfl,
      by show 736 + 512 ≤ 1696; omega⟩

theorem movCmp_ok {n : Nat} (hn : n < 2 ^ 64) {s : State} (hrdx : s.gpr .rdx = BitVec.ofNat 64 n) :
    WP isa (.block [.mov .rsi (.reg .r14), .alu .cmp .rdx (.imm 513)]) s fun s' =>
      s'.gpr .rsi = s.gpr .r14 ∧ (∀ r, r ≠ .rsi → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.mem = s.mem ∧ s'.cf = some (decide (n < 513)) := by
  rw [show ([.mov .rsi (.reg .r14), .alu .cmp .rdx (.imm 513)] : List Instr) =
    [.mov .rsi (.reg .r14)] ++ [.alu .cmp .rdx (.imm 513)] from rfl]
  refine WP.block_append (WP.mono (Stitch.movR_ok .rsi .r14) fun s₁ ⟨rsi₁, g₁, m₁, rd₁, wr₁, _, _⟩ => ?_)
  exact WP.mono (cmp513_ok hn (by rw [g₁ _ (by decide), hrdx])) fun s₂ ⟨g₂, rd₂, wr₂, m₂, c₂⟩ =>
    ⟨by rw [g₂, rsi₁], fun r hr => by rw [g₂, g₁ r hr], by rw [rd₂, rd₁], by rw [wr₂, wr₁], by rw [m₂, m₁], c₂⟩

/-- `cryptPre` for the 448 bytes: the arguments of the rest, and the
Poly1305 state kept. -/
theorem cryptPreR_ok (v : Proof.ChaCha20.X86_64.XorImpl) (hf448 : v.callee.fold = 448) {s₀ : State}
    (hp : APre e s₀) {s : State} (h : Inv s₀ s) (hpre : PreLen 448 (L s₀)) (hbig : 448 < L s₀)
    {key msg : List Byte} (hrep : Repr s.mem (off (cx s₀) 448) key msg) :
    WP isa (cryptPre v.callee.fold 512 v.callee.wide) s fun s' =>
      XArgsM s₀ 448 s' ∧ Repr s'.mem (off (cx s₀) 448) key msg := by
  have hm : mOf v.callee.fold 512 (L s₀) = 448 := by
    rw [mOf_big (by omega), hf448]
    simp only [splitOf, show (512 : Nat) ≠ 0 by decide, ite_false, ite_true]
    rw [ite_eq_left hpre]
  refine WP.mono (cryptPre_ok v (pass := 512) (.inr (.inr ⟨rfl, hf448⟩)) hp h)
    fun s₁ ⟨a₁, _, _, mx, fx, _, m₁⟩ => ?_
  rw [hm] at a₁ fx m₁
  have fw : Frame [sub s₀ 64 64] mx s₁.mem := by
    rw [m₁]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (contains_sub s₀ (by lit_omega) (by lit_omega) (by lit_omega))
  refine ⟨a₁, Repr.frame fw (fun r hr => ?_) (Repr.frame fx (fun r hr => ?_) hrep)⟩
  · simp only [List.mem_singleton] at hr; subst hr
    exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
  · simp only [List.mem_singleton] at hr; subst hr
    have hL9 : L s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
    exact (hp.c_d.sub_left (sub_ctx s₀ (by lit_omega))).sub_right (Region.sub_prefix (by omega))

/-- The 448 bytes whose keystream the prologue computed (`splitM` for `pass`
512), then the rest: `preS`, with `bulkP` or `tailS` on their permissions. -/
theorem preS_mid (v : Proof.ChaCha20.X86_64.XorImpl) (hf448 : v.callee.fold = 448) {s₀ : State} (hp : APre e s₀)
    {s : State} (h : Inv s₀ s) (hpre : PreLen 448 (L s₀)) (hbig : 448 < L s₀)
    (hst : stateAt s.mem (off (cx s₀) 64) = initState (K s₀) 0 (N s₀))
    (hks : ∀ k < 448, s.mem (off (cx s₀) (736 + k)) = (keystream (initState (K s₀) 1 (N s₀)) (L s₀)).getD k 0)
    {key msg : List Byte} (hrep : Repr s.mem (off (cx s₀) 448) key msg) :
    WP isa (preS { v.callee with pass := 512 }) s (DoneT 448 s₀ s key msg) := by
  have hL9 : L s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  have hm : mOf v.callee.fold 512 (L s₀) = 448 := by
    rw [mOf_big (by omega), hf448]
    simp only [splitOf, show (512 : Nat) ≠ 0 by decide, ite_false, ite_true]
    rw [ite_eq_left hpre]
  unfold preS
  refine WP.seq (WP.mono (cryptPre_ok v (pass := 512) (.inr (.inr ⟨rfl, hf448⟩)) hp h)
    fun s₁ ⟨a₁, cs₁, rd₁, mx, fx, dx, m₁⟩ => ?_)
  rw [hm] at a₁ fx dx m₁
  have fw : Frame [sub s₀ 64 64] mx s₁.mem := by
    rw [m₁]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (contains_sub s₀ (by lit_omega) (by lit_omega) (by lit_omega))
  have dpre : ∀ r ∈ [(⟨dp s₀, 448⟩ : Region)], (sub s₀ 64 64).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact (hp.c_d.sub_left (sub_ctx s₀ (by lit_omega))).sub_right (Region.sub_prefix (by omega))
  have st₁ : stateAt s₁.mem (off (cx s₀) 64) = ctr (initState (K s₀) 1 (N s₀)) 7 := by
    rw [m₁, stateAt_ctrW, stateAt_frame fx dpre, hst, show 448 / 64 + 1 = 7 + 1 from rfl, set12_ctr]
  have nctx : ∀ {k a n : Nat}, k < L s₀ → a + n ≤ 1696 → ¬ (sub s₀ a n).Contains (dp s₀ + BitVec.ofNat 64 k) 1 :=
    fun hk ha hc => hp.c_d _ (sub_ctx s₀ ha _ hc) (byte_dR hk)
  have m₁k : ∀ k < L s₀, s₁.mem (dp s₀ + BitVec.ofNat 64 k) = mx (dp s₀ + BitVec.ofNat 64 k) := fun k hk =>
    fw _ fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact nctx hk (by lit_omega)
  have rep₁ : Repr s₁.mem (off (cx s₀) 448) key msg := by
    refine Repr.frame fw (fun r hr => ?_) (Repr.frame fx (fun r hr => ?_) hrep)
    · simp only [List.mem_singleton] at hr; subst hr
      exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
    · simp only [List.mem_singleton] at hr; subst hr
      exact (hp.c_d.sub_left (sub_ctx s₀ (by lit_omega))).sub_right (Region.sub_prefix (by omega))
  refine WP.seq (WP.mono (movCmp_ok (n := L s₀ - 448) (by omega) a₁.rdx)
    fun s₂ ⟨rsi₂, g₂, rd₂, wr₂, m₂, c₂⟩ => ?_)
  -- Either branch, on the permissions of the chunks.
  have hl : Lay (cx s₀) (dp s₀) (L s₀) := ⟨hL9, hp.wrap_d, hp.c_d.sub_left (Region.sub_prefix (by decide))⟩
  have hw : Covers (bulkWr (cx s₀) (dp s₀) (L s₀)) s₂.wr := by
    rw [wr₂, a₁.wr]; exact bulk_covers' hp
  have cs₂ : ∀ r ∈ calleeSaved, s₂.gpr r = s.gpr r := fun r hr => by
    rw [g₂ r (by intro e; subst e; simp [calleeSaved] at hr), cs₁ r hr]
  have fin : ∀ {c : Prog isa}, c.noCalls = true →
      WP isa c (s₂.withRegions [] (bulkWr (cx s₀) (dp s₀) (L s₀)))
        (PreDone (cx s₀) (dp s₀) (L s₀) (s₂.withRegions [] (bulkWr (cx s₀) (dp s₀) (L s₀))) key msg) →
      WP isa c s₂ (DoneT 448 s₀ s key msg) := by
    intro c hn hc
    refine regionModel.wp_narrow hc (Covers.right hw) hw (Code.noFrames_of_noCalls hn) (.inl hn)
      fun _ s₃ _ rd₃ wr₃ f₃ hP => ?_
    have f₃' : Frame (bulkWr (cx s₀) (dp s₀) (L s₀)) s₂.mem s₃.mem := f₃
    have rd₃' : s₃.rd = s₂.rd := rd₃
    have wr₃' : s₃.wr = s₂.wr := wr₃
    have pd : PreDone (cx s₀) (dp s₀) (L s₀) (s₂.withRegions [] (bulkWr (cx s₀) (dp s₀) (L s₀))) key msg
      (s₃.withRegions [] (bulkWr (cx s₀) (dp s₀) (L s₀))) := hP
    obtain ⟨pdata, ppre, prepr, prbx, prbp, prdx, prcx, pr12, pr13, pr14, -, prsp, -, -⟩ := pd
    simp only [State.withRegions_gpr, State.withRegions_mem] at pdata ppre prepr prbx prbp prdx
    simp only [State.withRegions_gpr] at prcx pr12 pr13 pr14 prsp
    have ea : aOf 448 (L s₀) = aP (L s₀) := by
      simp only [aOf, aP]; rw [ite_eq_right (by omega), ite_eq_left hpre]; omega
    refine ⟨prdx, by rw [prcx, off_eq], fun r hr => ?_, by rw [rd₃', rd₂, rd₁],
      by rw [wr₃', wr₂, a₁.wr, h.wr], ?_, ?_,
      ⟨aP (L s₀), ea.symm, by simp only [aP]; omega, by simp only [aP]; omega, prbx, prbp,
        by rw [off_eq]; exact prepr⟩, .inl ⟨hbig, hpre⟩⟩
    · rcases hr with rfl | rfl | rfl | rfl
      · rw [pr12, cs₂ _ (by simp [calleeSaved])]
      · rw [pr13, cs₂ _ (by simp [calleeSaved])]
      · rw [pr14, cs₂ _ (by simp [calleeSaved])]
      · rw [prsp, cs₂ _ calleeSaved_rsp]
    · have e : sub s₀ 64 512 = ⟨cx s₀ + BitVec.ofNat 64 64, 512⟩ := by rw [sub, off_eq]
      have f₃'' : Frame [sub s₀ 64 512, sub s₀ 736 512, dR s₀] s₁.mem s₃.mem := by
        rw [← m₂]
        refine f₃'.sub fun r hr => ?_
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl
        · exact ⟨sub s₀ 64 512, by simp, by rw [e]; exact Offset.sub _ (by decide) (by decide)⟩
        · exact ⟨dR s₀, by simp, fun _ h => h⟩
        · exact ⟨sub s₀ 64 512, by simp, by rw [e]; exact Offset.sub _ (by decide) (by decide)⟩
        · exact ⟨sub s₀ 64 512, by simp, by rw [e]; exact Offset.sub _ (by decide) (by decide)⟩
        · exact ⟨sub s₀ 736 512, by simp, by
            rw [show kR (bfA (cx s₀)) = sub s₀ 736 512 by simp only [kR, kA, bfA, sub, off_eq, Offset.add_add]]
            exact fun _ h => h⟩
      refine (fx.sub fun r hr => ?_).trans ((fw.sub fun r hr => ?_).trans f₃'')
      · simp only [List.mem_singleton] at hr; subst hr
        exact ⟨dR s₀, by simp, Region.sub_prefix (by omega)⟩
      · simp only [List.mem_singleton] at hr; subst hr
        exact ⟨sub s₀ 64 512, by simp, sub_sub s₀ (Nat.le_refl _) (by lit_omega) (by lit_omega)⟩
    · rw [encrypt_eq, VG.Proof.Poly1305.length_bytesAt]
      apply VG.Proof.ChaCha20.bytesAt_xor (VG.Proof.ChaCha20.length_keystream _ _)
      intro k hk
      by_cases hk4 : k < 448
      · rw [ppre k hk4, m₂, m₁k k hk, dx k hk4, hks k hk4]
      · have x := pdata (k - 448) (by omega)
        rw [show 448 + (k - 448) = k by omega, m₂, m₁k k hk, fx _ fun r hr => ?_,
          show stA (cx s₀) = off (cx s₀) 64 by rw [off_eq], st₁,
          show L s₀ - 448 = L s₀ - 64 * 7 from rfl, show k - 448 = k - 64 * 7 from rfl,
          keystream_skip _ (by omega) hk] at x
        · exact x
        · simp only [List.mem_singleton] at hr; subst hr
          exact fun hc => Offset.disjoint_base (dp s₀) (d := k) (n := 1) (by omega)
            (by simp only [L] at hk; omega) _ (Region.contains_self _ _) hc
  have r14₂ : s₂.gpr .rsi = dp s₀ := by rw [rsi₂, cs₁ _ (by simp [calleeSaved]), h.r14]
  have bp : ∀ {σ : State}, σ = s₂.withRegions [] (bulkWr (cx s₀) (dp s₀) (L s₀)) →
      σ.wr = bulkWr (cx s₀) (dp s₀) (L s₀) ∧ σ.gpr .rsi = dp s₀ ∧
      σ.gpr .rdx = BitVec.ofNat 64 (L s₀ - 448) ∧ σ.gpr .rcx = bfA (cx s₀) ∧
      Repr σ.mem (psA (cx s₀)) key msg := by
    rintro σ rfl
    refine ⟨rfl, r14₂, by rw [State.withRegions_gpr, g₂ _ (by decide), a₁.rdx],
      by rw [State.withRegions_gpr, g₂ _ (by decide), a₁.rcx, off_eq], ?_⟩
    rw [State.withRegions_mem, m₂, show psA (cx s₀) = off (cx s₀) 448 by rw [off_eq]]; exact rep₁
  refine WP.ite (decide (L s₀ - 448 < 513)) (by simp [eval, c₂]) (fun hc => ?_) (fun hc => ?_)
  · simp only [decide_eq_true_eq] at hc
    obtain ⟨w₁, r₁, d₁, c₁, R₁⟩ := bp rfl
    exact fin (by generalize v.callee.vl = vl; cases vl <;> decide +kernel)
      (tailPS_ok _ hl (by omega) (by omega) w₁ r₁ d₁ c₁ R₁)
  · simp only [decide_eq_false_iff_not] at hc
    obtain ⟨w₁, r₁, d₁, c₁, R₁⟩ := bp rfl
    exact fin (by generalize v.callee.vl = vl; cases vl <;> decide +kernel) (bulkP_ok _ hl (by omega) (by omega) w₁ r₁ d₁ c₁ R₁)

theorem beq_ofNat_zero {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n == 0) = decide (n = 0) := by
  by_cases hn : n = 0
  · subst hn; rfl
  · have : BitVec.ofNat 64 n ≠ 0 := fun e => hn (by
      have := congrArg BitVec.toNat e
      rwa [Proof.Poly1305.X86_64.toNat_ofNat_lt h] at this)
    simp only [hn, decide_false]
    exact beq_false_of_ne this

theorem callIf_ok (v : Proof.ChaCha20.X86_64.XorImpl) {s₀ : State} (hp : APre e s₀) {s : State} (h : Inv s₀ s)
    {key msg : List Byte} {s₃ : State} (hq : (∃ E a, Mid v.callee.fold s₀ s key msg E a s₃) ∨ DoneT v.callee.fold s₀ s key msg s₃) :
    WP isa (.seq (.block [.alu .test .rdx (.reg .rdx)])
      (.ite .e (.block [.mov .rsi (.reg .rcx)]) (.call v.callee.name v.callee.code))) s₃
      (CryptedS v.callee.fold s₀ s key msg) := by
  have hL9 : L s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  refine WP.seq (WP.mono (testRdx_ok s₃) fun s₄ ⟨g₄, m₄, rd₄, wr₄, z₄⟩ => ?_)
  rcases hq with ⟨E, a, hm⟩ | hd
  · have hEL := hm.EL
    refine WP.ite (decide (L s₀ - E = 0)) (by simp only [eval, z₄, hm.rdx, beq_ofNat_zero (show L s₀ - E < 2 ^ 64 by omega)])
      (fun hc => ?_) (fun hc => ?_)
    · simp only [decide_eq_true_eq] at hc
      refine WP.mono (Stitch.movR_ok .rsi .rcx) fun s₅ ⟨rsi₅, g₅, m₅, rd₅, wr₅, _, _⟩ => ?_
      have gg : ∀ r, r ≠ .rsi → s₅.gpr r = s₃.gpr r := fun r hr => by rw [g₅ r hr, g₄]
      refine ⟨by rw [rsi₅, g₄, hm.rcx], fun r hr => ?_, by rw [rd₅, rd₄, hm.rd], by rw [wr₅, wr₄, hm.wr],
        by rw [m₅, m₄]; exact hm.frame.mono (by simp), ?_,
        ⟨a, hm.aO, hm.a16, Nat.le_trans hm.aE hEL, by rw [gg _ (by decide), hm.rbx],
          by rw [gg _ (by decide), hm.rbp], by rw [m₅, m₄]; exact hm.repr⟩⟩
      · rw [gg r (by rcases hr with rfl | rfl | rfl | rfl <;> decide), hm.keep r hr]
      · rw [m₅, m₄, encrypt_eq, VG.Proof.Poly1305.length_bytesAt]
        apply VG.Proof.ChaCha20.bytesAt_xor (VG.Proof.ChaCha20.length_keystream _ _)
        intro k hk
        rw [hm.data k hk, ite_eq_left (by omega)]
    · exact call_mid v hp h ⟨by rw [g₄, hm.rdi], by rw [g₄, hm.rcx], by rw [g₄, hm.rsi], by rw [g₄, hm.rdx],
        by rw [g₄, hm.rbx], by rw [g₄, hm.rbp], fun r hr => by rw [g₄, hm.keep r hr], by rw [rd₄, hm.rd],
        by rw [wr₄, hm.wr], hm.E64, hm.Ediv, hm.aEq, hm.EL, hm.aE, hm.a16, hm.aO, by rw [m₄, hm.st],
        fun k hk => by rw [m₄, hm.data k hk], by rw [m₄]; exact hm.frame, by rw [m₄]; exact hm.repr⟩
  · refine WP.ite true (by simp only [eval, z₄, hd.rdx]; rfl) (fun _ => ?_) (fun hc => by simp at hc)
    refine WP.mono (Stitch.movR_ok .rsi .rcx) fun s₅ ⟨rsi₅, g₅, m₅, rd₅, wr₅, _, _⟩ => ?_
    have gg : ∀ r, r ≠ .rsi → s₅.gpr r = s₃.gpr r := fun r hr => by rw [g₅ r hr, g₄]
    obtain ⟨a, aO, a16, aL, rbx, rbp, repr⟩ := hd.abs
    refine ⟨by rw [rsi₅, g₄, hd.rcx], fun r hr => ?_, by rw [rd₅, rd₄, hd.rd], by rw [wr₅, wr₄, hd.wr],
      by rw [m₅, m₄]; exact hd.frame.mono (by simp), by rw [m₅, m₄]; exact hd.data,
      ⟨a, aO, a16, aL, by rw [gg _ (by decide), rbx], by rw [gg _ (by decide), rbp], by rw [m₅, m₄]; exact repr⟩⟩
    rw [gg r (by rcases hr with rfl | rfl | rfl | rfl <;> decide), hd.keep r hr]

/-- `Inv.step`, for a part that may change `rbx` and `rbp`. -/
theorem Inv.step' {s₀ s s' : State} (h : Inv s₀ s)
    (cs : ∀ r, r = .r12 ∨ r = .r13 ∨ r = .r14 ∨ r = .r15 ∨ r = .rsp → s'.gpr r = s.gpr r)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) {rs : List Region} (hf : Frame rs s.mem s'.mem)
    (hsub : ∀ r ∈ rs, ∃ r' ∈ [workR s₀, dR s₀, stkR s₀], Region.Sub r r')
    (hsv : ∀ r ∈ rs, (sub s₀ 0 48).Disjoint r) : Inv s₀ s' where
  r15 := by rw [cs _ (by simp), h.r15]
  r14 := by rw [cs _ (by simp), h.r14]
  r13 := by rw [cs _ (by simp), h.r13]
  r12 := by rw [cs _ (by simp), h.r12]
  rsp := by rw [cs _ (by simp), h.rsp]
  rd := by rw [hrd, h.rd]
  wr := by rw [hwr, h.wr]
  saved := h.saved.frame hf hsv
  frame := h.frame.trans (hf.sub hsub)

/-- The implementation of `vg_chacha20_xor` that comes with the AVX2
`vg_poly1305_blocks`, the only one `sealFor` stitches. -/
theorem avx2_of (v : Proof.ChaCha20.X86_64.XorImpl) (hv : v.poly = .avx2) :
    v.callee.fold = 448 ∧ v.callee.pass = 0 ∧ v.callee.wide = 5 := by
  rcases v.fold_poly with ⟨-, -, -, h⟩ | ⟨hf, hp, hw, -⟩ | ⟨-, -, -, h | h⟩
  · rw [hv] at h; cases h
  · exact ⟨hf, hp, hw⟩
  · rw [hv] at h; cases h
  · rw [hv] at h; cases h

theorem cryptS_mx (v : Proof.ChaCha20.X86_64.XorImpl) (hv : v.poly = .avx2) :
    (cryptS { v.callee with pass := 512 }).allInstrs (fun i => !loadsMxcsr i) = true := by
  obtain ⟨hf, -, hw⟩ := avx2_of v hv
  rcases Bool.eq_false_or_eq_true v.callee.vl with hl | hl <;>
    (simp only [cryptS, preS, Code.allInstrs, v.mxcsr, hf, hw, hl]; lit_decide)

theorem prologueP_mx (v : Proof.ChaCha20.X86_64.XorImpl) (hv : v.poly = .avx2) :
    (prologue { v.callee with pass := 512 }).allInstrs (fun i => !loadsMxcsr i) = true := by
  obtain ⟨hf, -, hw⟩ := avx2_of v hv
  simp only [prologue, Code.allInstrs, v.mxcsr, hf, hw]; lit_decide

/-- `cryptS`'s branch on the length. -/
def cryptIteS (x : Impl.ChaCha20.X86_64.Callee) : Prog isa :=
  .ite .b
    (.seq (.block (ptr .rsi .r15 736 ++ ([.mov .rdx (.reg .r13)] : List Instr)))
      (.seq (xorBufX x.wide .r14) (.block (ptr .rsi .r15 128 ++ whole))))
    (.seq (.block mLoad)
    (.seq (.block [.alu .test .rdx (.reg .rdx)])
      (.seq (.ite .e (bigS x.vl) (preS x))
        (.seq (.block [.alu .test .rdx (.reg .rdx)])
          (.ite .e (.block [.mov .rsi (.reg .rcx)]) (.call x.name x.code))))))

theorem cryptS_eq (x : Impl.ChaCha20.X86_64.Callee) : cryptS x =
    .seq (.block [.alu .cmp .r13 (.imm (BitVec.ofNat 32 (x.fold + 1)))]) (.seq (cryptIteS x)
      (.seq (.block (anchor .rsi 128)) (.seq (wipeL x.fold 512)
        (.seq (.block [.alu .add .rdx (.imm 64)]) (zeroKs x.wide))))) := rfl

/-- `cryptS`'s branch on the length: the data encrypted, and its first `a`
bytes of ciphertext absorbed, the keystream not yet wiped. -/
theorem cryptIte_ok (v : Proof.ChaCha20.X86_64.XorImpl) (hv : v.poly = .avx2) {s₀ : State} (hp : APre e s₀)
    {s₁ : State} (h₁ : Inv s₀ s₁) (c₁ : s₁.cf = some (decide (L s₀ < v.callee.fold + 1)))
    (hst : stateAt s₁.mem (off (cx s₀) 64) = initState (K s₀) 0 (N s₀))
    (hks : ∀ k < mOf v.callee.fold 512 (L s₀), s₁.mem (off (cx s₀) (736 + k)) =
      (keystream (initState (K s₀) 1 (N s₀)) (L s₀)).getD k 0)
    (hms : s₁.mem.readW (off (cx s₀) 48) 64 = BitVec.ofNat 64 (mOf v.callee.fold 512 (L s₀)))
    {key msg : List Byte} (hrep : Repr s₁.mem (off (cx s₀) 448) key msg) :
    WP isa (cryptIteS { v.callee with pass := 512 }) s₁ (CryptedS v.callee.fold s₀ s₁ key msg) := by
  have hfl := v.fold_le
  have hf := (avx2_of v hv).1
  have hL9 : L s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  have hm := mOf_le v.callee.fold 512 (L s₀)
  unfold cryptIteS
  refine WP.ite (decide (L s₀ < v.callee.fold + 1)) (by simp [eval, c₁]) (fun hc => ?_) (fun hc => ?_)
  · simp only [decide_eq_true_eq] at hc
    apply seq3
    refine WP.mono (cryptSmall_ok hfl (wide_of v) hp h₁ (by omega) hks) fun s₃ c₃ => ?_
    refine WP.mono (whole_ok s₃) fun s₄ ⟨rbx₄, rbp₄, g₄, rd₄, wr₄, m₄⟩ => ?_
    have cs : ∀ r, r = .r12 ∨ r = .r13 ∨ r = .r14 ∨ r = .rsp → s₄.gpr r = s₁.gpr r := fun r hr => by
      rcases hr with rfl | rfl | rfl | rfl <;>
        rw [g₄ _ (by decide) (by decide), c₃.cs _ (by simp [calleeSaved]) (by decide)]
    have f₄ : Frame [sub s₀ 64 384, dR s₀, stkR s₀] s₁.mem s₄.mem := by rw [m₄]; exact c₃.frame
    refine ⟨by rw [g₄ _ (by decide) (by decide), c₃.rsi], cs, by rw [rd₄, c₃.rd], by rw [wr₄, c₃.wr],
      f₄.sub fun r hr => ?_, by rw [m₄]; exact c₃.data, 0, by simp only [aOf]; rw [ite_eq_left (by omega)], rfl, Nat.zero_le _,
      by rw [rbx₄, c₃.cs _ (by simp [calleeSaved]) (by decide), h₁.r14]; simp,
      by rw [rbp₄, c₃.cs _ (by simp [calleeSaved]) (by decide), h₁.r13, hL, Nat.sub_zero], ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨sub s₀ 64 512, by simp, sub_sub s₀ (Nat.le_refl _) (by lit_omega) (by lit_omega)⟩
      · exact ⟨dR s₀, by simp, fun _ h => h⟩
      · exact ⟨stkR s₀, by simp, fun _ h => h⟩
    · rw [show bytesAt s₄.mem (dp s₀) 0 = [] from rfl, List.append_nil]
      refine Repr.frame f₄ (fun r hr => ?_) hrep
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
      · exact hp.c_d.sub_left (sub_ctx s₀ (by lit_omega))
      · exact (hp.stk_sub (by lit_omega)).symm
  · simp only [decide_eq_false_iff_not] at hc
    -- `m`: 448 if the prologue computed the keystream of the first 448 bytes, else 0.
    refine WP.seq (WP.mono (mLoad_ok (n := mOf v.callee.fold 512 (L s₀)) h₁.r15 (by rw [h₁.wr]; exact hp.in_ctx (a := 48) (w := 8) (by lit_omega))
      hms) fun s₂ ⟨d₂, g₂, rd₂, wr₂, m₂⟩ => ?_)
    refine WP.seq (WP.mono (testRdx_ok s₂) fun s₃ ⟨g₃, m₃, rd₃, wr₃, z₃⟩ => ?_)
    have g13 : ∀ r, r ≠ .rdx → s₃.gpr r = s₁.gpr r := fun r hr => by rw [g₃, g₂ r hr]
    have h₃ : Inv s₀ s₃ := h₁.step (fun r hr => g13 r (by rintro rfl; simp [calleeSaved] at hr))
      (by rw [rd₃, rd₂]) (by rw [wr₃, wr₂]) (rs := []) (by rw [m₃, m₂]; exact Frame.refl _ _)
      (fun _ h => by simp at h) (fun _ h => by simp at h)
    have mm : s₃.mem = s₁.mem := by rw [m₃, m₂]
    refine WP.mono (Q := CryptedS v.callee.fold s₀ s₃ key msg) ?_ fun s' c =>
      ⟨c.rsi, fun r hr => by
        rw [c.keep r hr, g13 r (by rcases hr with rfl | rfl | rfl | rfl <;> decide)],
        by rw [c.rd, rd₃, rd₂], by rw [c.wr, wr₃, wr₂], by rw [← mm]; exact c.frame,
        by rw [← mm]; exact c.data, c.abs⟩
    have hst₃ : stateAt s₃.mem (off (cx s₀) 64) = initState (K s₀) 0 (N s₀) := by rw [mm]; exact hst
    have hrep₃ : Repr s₃.mem (off (cx s₀) 448) key msg := by rw [mm]; exact hrep
    refine WP.seq (WP.mono (Q := fun (s₄ : State) => (∃ E a, Mid v.callee.fold s₀ s₃ key msg E a s₄) ∨
      DoneT v.callee.fold s₀ s₃ key msg s₄) ?_ fun s₄ hq => callIf_ok v hp h₃ hq)
    have hMv : mOf v.callee.fold 512 (L s₀) = if PreLen 448 (L s₀) then 448 else 0 := by
      rw [mOf_big (by omega), hf]
      simp only [splitOf, show (512 : Nat) ≠ 0 by decide, ite_false, ite_true]
    refine WP.ite (decide (mOf v.callee.fold 512 (L s₀) = 0))
      (by simp only [eval, z₃, d₂, beq_ofNat_zero (show mOf v.callee.fold 512 (L s₀) < 2 ^ 64 by omega)])
      (fun hz => ?_) (fun hz => ?_)
    · -- None: the whole chunks by `bulk`.
      simp only [decide_eq_true_eq] at hz
      have hnp : ¬ PreLen v.callee.fold (L s₀) := by
        rw [hMv] at hz; rw [hf]; split at hz
        · omega
        · assumption
      unfold bigS
      refine WP.seq (WP.mono (Q := fun (s₄ : State) => Args s₀ s₃ s₄ ∧ s₄.cf = some (decide (L s₀ < 512))) ?_
        fun s₄ ⟨ha, cf₄⟩ => ?_)
      · refine WP.block_append (WP.mono (cryptA_ok hp h₃) fun s₂ ⟨m₂, rdi₂, rsi₂, rdx₂, rcx₂, cs₂, rd₂, wr₂⟩ =>
          WP.mono (cmp512_ok hL9 (by rw [rdx₂, hL])) fun s₃ ⟨g₃, rd₃, wr₃, m₃, c₃⟩ => ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_,
            fun r hr => ?_, by rw [rd₃, rd₂], by rw [wr₃, wr₂]⟩, c₃⟩)
        · rw [m₃, m₂]
        · rw [g₃, rdi₂]
        · rw [g₃, rsi₂]
        · rw [g₃, rdx₂, hL]
        · rw [g₃, rcx₂]
        · rw [g₃, cs₂ _ (by simp [calleeSaved]), h₃.r13, hL]
        · rw [g₃, cs₂ _ (by simp [calleeSaved]), h₃.r14]
        · rw [g₃, cs₂ r (by rcases hr with rfl | rfl | rfl | rfl <;> simp [calleeSaved])]
      refine WP.ite (decide (L s₀ < 512)) (by simp [eval, cf₄]) (fun hc' => ?_) (fun hc' => ?_)
      · simp only [decide_eq_true_eq] at hc'
        exact WP.mono (whole_mid hp ha hnp hc' hst₃ hrep₃) fun s₄ hm₄ => .inl ⟨0, 0, hm₄⟩
      · simp only [decide_eq_false_iff_not] at hc'
        exact bulk_mid _ hp (by rw [wr₃, wr₂, h₁.wr]) ha (by omega) hnp (by omega) hst₃ hrep₃
    · -- 448: those by `cryptPre`, the rest by `bulkP` or `tailS`.
      simp only [decide_eq_false_iff_not] at hz
      have hpre : PreLen 448 (L s₀) := by
        rw [hMv] at hz; split at hz
        · assumption
        · omega
      have h448 : mOf v.callee.fold 512 (L s₀) = 448 := by rw [hMv, ite_eq_left hpre]
      refine WP.mono (preS_mid v hf hp h₃ hpre (by omega) hst₃
        (fun k hk => by rw [mm]; exact hks k (by rw [h448]; exact hk)) hrep₃) fun s₄ d => .inr ?_
      rw [hf]; exact d

/-- The data encrypted, by `bulk` and the implementation `v` of
`vg_chacha20_xor`, its first `a` bytes of ciphertext absorbed, and the
keystream wiped. -/
theorem cryptS_ok (v : Proof.ChaCha20.X86_64.XorImpl) (hv : v.poly = .avx2) {s₀ : State} (hp : APre e s₀)
    {s : State} (h : Inv s₀ s)
    (hst : stateAt s.mem (off (cx s₀) 64) = initState (K s₀) 0 (N s₀))
    (hks : ∀ k < mOf v.callee.fold 512 (L s₀), s.mem (off (cx s₀) (736 + k)) =
      (keystream (initState (K s₀) 1 (N s₀)) (L s₀)).getD k 0)
    (hms : s.mem.readW (off (cx s₀) 48) 64 = BitVec.ofNat 64 (mOf v.callee.fold 512 (L s₀)))
    {key msg : List Byte} (hrep : Repr s.mem (off (cx s₀) 448) key msg) :
    WP isa (cryptS { v.callee with pass := 512 }) s fun s' => Inv s₀ s' ∧
      Frame [sub s₀ 64 512, sub s₀ 672 1024, dR s₀, stkR s₀] s.mem s'.mem ∧
      bytesAt s'.mem (dp s₀) (L s₀) = Spec.ChaCha20.encrypt (K s₀) 1 (N s₀) (bytesAt s.mem (dp s₀) (L s₀)) ∧
      ∃ a, a = aOf v.callee.fold (L s₀) ∧ a % 16 = 0 ∧ a ≤ L s₀ ∧ s'.gpr .rbx = dp s₀ + BitVec.ofNat 64 a ∧
        s'.gpr .rbp = BitVec.ofNat 64 (L s₀ - a) ∧
        Repr s'.mem (off (cx s₀) 448) key (msg ++ bytesAt s'.mem (dp s₀) a) := by
  have hfl := v.fold_le
  have hf := (avx2_of v hv).1
  have hP : PassOk v.callee.fold 512 := .inr (.inr ⟨rfl, hf⟩)
  have hL9 : L s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  have hm := mOf_le v.callee.fold 512 (L s₀)
  rw [cryptS_eq]
  refine WP.seq (WP.mono (cmpFold_ok (fold := v.callee.fold) (by lit_omega) h.r13)
    fun s₁ ⟨g₁, rd₁, wr₁, m₁, c₁⟩ => ?_)
  have h₁ : Inv s₀ s₁ := h.step (fun r _ => by rw [g₁]) rd₁ wr₁ (rs := []) (by rw [m₁]; exact Frame.refl _ _)
    (fun _ h => by simp at h) (fun _ h => by simp at h)
  refine WP.seq (WP.mono (Q := CryptedS v.callee.fold s₀ s₁ key msg)
    (cryptIte_ok v hv hp h₁ c₁ (by rw [m₁]; exact hst) (by rw [m₁]; exact hks) (by rw [m₁]; exact hms)
      (by rw [m₁]; exact hrep)) fun s₂ c₂ => ?_)
  -- The keystream wiped, as in `crypt_ok`.
  refine WP.seq (WP.mono (anchor_ok .rsi (k := 128) (by lit_omega) s₂) fun s₃ ⟨e3, g₃, rd₃, wr₃, m₃⟩ => ?_)
  have cs₃ : ∀ r, r = .r12 ∨ r = .r13 ∨ r = .r14 ∨ r = .r15 ∨ r = .rsp → s₃.gpr r = s.gpr r := fun r hr => by
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [g₃ _ (by decide), c₂.keep _ (.inl rfl), g₁]
    · rw [g₃ _ (by decide), c₂.keep _ (.inr (.inl rfl)), g₁]
    · rw [g₃ _ (by decide), c₂.keep _ (.inr (.inr (.inl rfl))), g₁]
    · rw [e3, c₂.rsi, off_sub, h.r15]
    · rw [g₃ _ (by decide), c₂.keep _ (.inr (.inr (.inr rfl))), g₁]
  have fc : Frame [sub s₀ 64 512, sub s₀ 736 512, dR s₀, stkR s₀] s.mem s₃.mem := by
    rw [m₃, ← m₁]; exact c₂.frame
  have i₃ : Inv s₀ s₃ := Inv.step' h cs₃ (by rw [rd₃, c₂.rd, rd₁]) (by rw [wr₃, c₂.wr, wr₁]) fc (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact sub_work s₀ (by lit_omega) (by lit_omega)
      · exact sub_work s₀ (by lit_omega) (by lit_omega)
      · exact ⟨dR s₀, by simp, fun _ h => h⟩
      · exact stk_work s₀) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
      · exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
      · exact hp.c_d.sub_left (sub_ctx s₀ (by lit_omega))
      · exact (hp.stk_sub (by lit_omega)).symm)
  refine WP.seq (WP.mono (wipeL_ok (fold := v.callee.fold) (extra := 512) (by lit_omega) (by decide) i₃.r13)
    fun s₄ ⟨d₄, g₄, rd₄, wr₄, m₄⟩ => ?_)
  refine WP.seq (WP.mono (add64_ok (n := wOf v.callee.fold 512 (L s₀)) d₄) fun s₅ ⟨d₅, g₅, rd₅, wr₅, m₅⟩ => ?_)
  refine WP.mono (zeroKs_ok (wide_of v) hp (n := 64 + wOf v.callee.fold 512 (L s₀)) (by omega) (by simp only [wOf]; split <;> lit_omega) d₅
    (by rw [g₅ _ (by decide), g₄ _ (by decide), i₃.r15]) (by rw [wr₅, wr₄, i₃.wr]))
    fun s₆ ⟨g₆, rd₆, wr₆, f₆, _⟩ => ?_
  have g36 : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → s₆.gpr r = s₃.gpr r := fun r h1 h2 h3 => by
    rw [g₆ r h1 h2, g₅ r h3, g₄ r h3]
  have f₅₆ : Frame [sub s₀ 672 1024] s₃.mem s₆.mem := by rw [← m₄, ← m₅]; exact f₆
  have hbd : ∀ n, n ≤ L s₀ → bytesAt s₆.mem (dp s₀) n = bytesAt s₃.mem (dp s₀) n := fun n hn =>
    bytesAt_frame f₅₆ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ((hp.c_d.sub_left (sub_ctx s₀ (by lit_omega))).symm).sub_left (Region.sub_prefix hn)) (by omega)
  obtain ⟨a, aO, a16, aL, rbx₂, rbp₂, repr₂⟩ := c₂.abs
  refine ⟨Inv.step' i₃ (fun r hr => g36 r (by rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide) (by rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide))
      (by rw [rd₆, rd₅, rd₄]) (by rw [wr₆, wr₅, wr₄]) f₅₆
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact sub_work s₀ (by lit_omega) (by lit_omega))
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)),
    ?_, ?_, a, aO, a16, aL, by rw [g36 _ (by decide) (by decide) (by decide), g₃ _ (by decide), rbx₂],
    by rw [g36 _ (by decide) (by decide) (by decide), g₃ _ (by decide), rbp₂], ?_⟩
  · refine (fc.sub fun r hr => ?_).trans (f₅₆.sub fun r hr => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨sub s₀ 672 1024, by simp, sub_sub s₀ (by decide) (by decide) (by decide)⟩
      · exact ⟨dR s₀, by simp, fun _ h => h⟩
      · exact ⟨stkR s₀, by simp, fun _ h => h⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩
  · rw [hbd _ (Nat.le_refl _), m₃, c₂.data, m₁]
  · rw [hbd a aL]
    refine Repr.frame f₅₆ (fun r hr => ?_) (by rw [m₃]; exact repr₂)
    simp only [List.mem_singleton] at hr; subst hr
    exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)

end VG.Proof.ChaCha20Poly1305.X86_64.Stitch

/-!
# ChaCha20 and Poly1305 together (x86-64): `sealStitched` is correct

As `seal_correct`, with `cryptS` (`cryptS_ok`) in place of `crypt`: the
ciphertext it has absorbed, a multiple of 16 bytes, and the rest that
`macPadLengths` absorbs make up the padded ciphertext.
-/

namespace VG.Proof.ChaCha20Poly1305.X86_64.Stitch

open VG VG.X86_64 VG.Impl.ChaCha20Poly1305.X86_64 VG.Impl.ChaCha20Poly1305.X86_64.Stitch
open VG.Spec.Poly1305 (Repr bytesAt mac leBytes)
open VG.Spec.ChaCha20 (stateAt)
open VG.Spec.ChaCha20Poly1305 (pad16 macData polyKeyGen)

variable {e : Bool}

/-- The data after its first `a` bytes. -/
theorem srcRest {s₀ : State} (hp : APre e s₀) {a : Nat} (ha : a ≤ L s₀) :
    Src s₀ (dp s₀ + BitVec.ofNat 64 a) (L s₀ - a) := by
  have hL9 : L s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  have dsub : Region.Sub ⟨dp s₀ + BitVec.ofNat 64 a, L s₀ - a⟩ (dR s₀) := Offset.sub_base _ (by omega)
  refine ⟨by omega, Nat.le_trans (Nat.add_le_add_right (toNat_add_le _ a (by omega)) _)
    (by have := hp.wrap_d; omega), hp.c_d.sub_right dsub, hp.stk_d.sub_right dsub, Covers.right ?_⟩
  refine Covers.of_sub fun r hr => ?_
  simp only [List.mem_singleton] at hr; subst hr
  exact ⟨dR s₀, hp.d_wr, a, rfl, by show a + (L s₀ - a) ≤ L s₀; omega⟩

/-- A message absorbed in two parts, the first a multiple of 16 bytes, padded. -/
theorem split_pad (m : Mem) (p : Addr) {a n : Nat} (ha : a % 16 = 0) (hn : a ≤ n) :
    bytesAt m p a ++ (bytesAt m (p + BitVec.ofNat 64 a) (n - a) ++ pad16 (bytesAt m (p + BitVec.ofNat 64 a) (n - a))) =
      bytesAt m p n ++ pad16 (bytesAt m p n) := by
  have e : bytesAt m p n = bytesAt m p a ++ bytesAt m (p + BitVec.ofNat 64 a) (n - a) := by
    rw [← VG.Proof.Poly1305.bytesAt_add, Nat.add_sub_cancel' hn]
  have hp : pad16 (bytesAt m (p + BitVec.ofNat 64 a) (n - a)) = pad16 (bytesAt m p n) := by
    simp only [pad16, VG.Proof.Poly1305.length_bytesAt, show (n - a) % 16 = n % 16 by omega]
  rw [hp, e, List.append_assoc]

theorem sealStitched_correct (v : Proof.ChaCha20.X86_64.XorImpl) (hv : v.poly = .avx2) {s₀ : State}
    (hp : APre true s₀) :
    WP isa (sealStitched { v.callee with pass := 512 } v.poly) s₀ fun s' =>
      abiPreserved s₀ s' ∧ sealX86_64.post s₀ s' := by
  have hL' := (Nat.le_of_lt (s₀.gpr .r9).isLt)
  have hP : PassOk v.callee.fold 512 := .inr (.inr ⟨rfl, (avx2_of v hv).1⟩)
  refine WP.seq (WP.mono_mx (by decide +kernel) (entry_ok hp) fun s₀' e₀ mx₀ => ?_)
  subst e₀
  refine WP.seq (WP.mono_mx (prologueP_mx v hv) (prologueP_ok v hP hp) fun s₁ h₁ mx₁ => ?_)
  have hA : bytesAt s₁.mem (ad s₀) (AL s₀) = A s₀ :=
    bytesAt_frame h₁.fine (by rdisj_all) (Nat.le_of_lt (s₀.gpr .rcx).isLt)
  refine WP.seq (WP.mono (macPad_ok v.poly hp (p := .rbx) (n := .rbp) ⟨.inl rfl, .inl rfl⟩ (srcA hp)
    h₁.inv.r15 h₁.inv.rsp h₁.inv.rd h₁.inv.wr h₁.rbx (by rw [h₁.rbp]; exact hRDX s₀))
    fun s₂ ⟨cs₂, rd₂, wr₂, f₂, mx₂, r₂⟩ => ?_)
  have i₂ := mac_inv hp h₁.inv cs₂ rd₂ wr₂ f₂
  refine WP.seq (WP.mono_mx (by decide +kernel) (lengths_ok hp i₂ (by rw [cs₂ _ (by simp [calleeSaved]), h₁.rbp]))
    fun s₃ ⟨i₃, _, f₃, len₃⟩ mx₃ => ?_)
  have st₃ : stateAt s₃.mem (off (cx s₀) 64) = Spec.ChaCha20.initState (K s₀) 0 (N s₀) := by
    rw [stateAt_frame f₃ (by rdisj_all), stateAt_frame f₂ (by rdisj_all), h₁.st]
  have D₃ : bytesAt s₃.mem (dp s₀) (L s₀) = D s₀ := by
    rw [bytesAt_frame f₃ (by rdisj_all) hL', bytesAt_frame f₂ (by rdisj_all) hL',
      bytesAt_frame h₁.fine (by rdisj_all) hL']
  have hM := Nat.le_trans (mOf_le v.callee.fold 512 (L s₀)) v.fold_le
  have ks₃ := ks_frame f₃ (by rdisj_all) hM (ks_frame f₂ (by rdisj_all) hM h₁.ks)
  have R₃ := Repr.frame f₃ (by rdisj_all) (r₂ (otk s₀) [] h₁.poly)
  have ms₃ : s₃.mem.readW (off (cx s₀) 48) 64 = BitVec.ofNat 64 (mOf v.callee.fold 512 (L s₀)) := by
    rw [f₃.readW (r := sub s₀ 48 8) (Region.contains_self _ _) (by rdisj_all) (by decide),
      f₂.readW (r := sub s₀ 48 8) (Region.contains_self _ _) (by rdisj_all) (by decide)]
    exact h₁.mslot rfl
  refine WP.seq (WP.mono_mx (cryptS_mx v hv) (cryptS_ok v hv hp i₃ st₃ ks₃ ms₃ R₃)
    fun s₄ ⟨i₄, f₄, ct₄, a, _, a16, aL, rbx₄, rbp₄, R₄⟩ mx₄ => ?_)
  rw [D₃] at ct₄
  refine WP.seq (WP.mono (macPadLengths_ok v.poly hp (p := .rbx) (n := .rbp) ⟨.inl rfl, .inl rfl⟩
    (srcRest hp aL) i₄ rbx₄ rbp₄)
    fun s₆ ⟨i₆, _, f₆, mx₆, r₆⟩ => ?_)
  refine WP.seq (WP.mono_mx (by decide +kernel) (finalizeTag_ok hp i₆)
    fun s₇ ⟨cs₇, rd₇, wr₇, rdi₇, f₇, tag₇⟩ mx₇ => ?_)
  refine WP.mono_mx (by decide +kernel) (restore_ok hp rdi₇ (i₆.saved.frame f₇ (by rdisj_all))
    (by rw [cs₇ _ calleeSaved_rsp, i₆.rsp])
    (by rw [rd₇, i₆.rd]) (by rw [wr₇, i₆.wr])) fun s₈ ⟨cs₈, _, m₈⟩ mx₈ => ?_
  have T₇ := tag₇ _ _ (r₆ _ _ R₄)
  have L₄ : bytesAt s₄.mem (off (cx s₀) 592) 16 = leBytes 8 (AL s₀) ++ leBytes 8 (L s₀) := by
    rw [bytesAt_frame f₄ (by rdisj_all) (by lit_omega), len₃]
  have C₈ : bytesAt s₈.mem (dp s₀) (L s₀) = Spec.ChaCha20.encrypt (K s₀) 1 (N s₀) (D s₀) := by
    rw [m₈, bytesAt_frame f₇ (by rdisj_all) hL', bytesAt_frame f₆ (by rdisj_all) hL', ct₄]
  have C₄ : bytesAt s₄.mem (dp s₀) (L s₀) = Spec.ChaCha20.encrypt (K s₀) 1 (N s₀) (D s₀) := ct₄
  refine ⟨⟨cs₈, by rw [m₈]; exact ret_kept hp i₆.frame hp.ret_t f₇,
    by rw [mx₈, mx₇, mx₆, mx₄, mx₃, mx₂, mx₁, mx₀]⟩, ?_⟩
  show Spec.ChaCha20Poly1305.encrypt (K s₀) (N s₀) (A s₀) (D s₀) =
    (bytesAt s₈.mem (dp s₀) (L s₀), bytesAt s₈.mem (tp s₀) 16)
  rw [C₈, m₈, T₇, L₄, List.append_assoc ([] ++ _), split_pad _ _ a16 aL, C₄, hA]
  simp only [Spec.ChaCha20Poly1305.encrypt, macData, List.nil_append,
    List.append_assoc, VG.Proof.Poly1305.length_bytesAt, length_encrypt]

end VG.Proof.ChaCha20Poly1305.X86_64.Stitch
