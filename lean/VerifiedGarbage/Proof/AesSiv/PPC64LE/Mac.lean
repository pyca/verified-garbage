module

public import VerifiedGarbage.Proof.AesSiv.PPC64LE.Env
import VerifiedGarbage.Proof.AesCtr.PPC64LE.Call
public import VerifiedGarbage.Impl.AesSiv.PPC64LE
public import VerifiedGarbage.Spec.Siv
import VerifiedGarbage.Proof.AesSiv.CtrPart
import VerifiedGarbage.Proof.Siv.Spec
public import VerifiedGarbage.Proof.Cmac.Block
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Cmac.Stream
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.AesCcm.PPC64LE.Wp
public import VerifiedGarbage.Proof.AesCbc.Spec
public import VerifiedGarbage.Proof.CmacAes.Stream.PPC64LE.Common
public import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Spec.Aes
public import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
public import VerifiedGarbage.Proof.CmacAes.PPC64LE.Verified
import VerifiedGarbage.Proof.CmacAes.PPC64LE.Subkeys
import VerifiedGarbage.Proof.AesCbc.PPC64LE.Body
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec

/-! ### `AesSiv.PPC64LE.FinRaw`, which this module and modules that import it used -/

section

/-!
# AES-SIV on PPC64LE: `vg_cmac_aes_finalize` with any subkeys

Untrusted: everything here is checked by Lean. `vg_cmac_aes_finalize`'s
contract states the MAC only when the subkeys after the key schedule are
the schedule's own; S2V's PRF (`Spec.Siv.ctxMac`) uses whatever subkeys the
key context holds. Its proof (`Proof/CmacAes/PPC64LE/Verified.lean`) shows
more: the state becomes `CIPH_K(C ⊕ Mₙ)` with `Mₙ` the last block formed
from the subkeys in memory (`mn`). That is the contract here
(`finRawPPC64LE`), proven the same way, and the call lemma `fin_call_raw`.
-/

@[expose] public section

namespace VG.Proof.AesSiv.PPC64LE

open VG VG.PPC64LE VG.Impl.CmacAes.PPC64LE
open VG.Proof.CmacAes.PPC64LE (FPre finalizePPC64LE finPre_wp fin_bound slots_scr finMem_frame mn wr_in
  ciphAt cipher_bytes preserved_ne)
open VG.Proof.CmacAes.Stream.PPC64LE (FArgs finalize_noFrames)
open VG.Proof.AesCbc.PPC64LE (blk_call callEntry_gpr' toNat_rounds)
open VG.Spec.Aes (bytesAt)

/-- `vg_cmac_aes_finalize`, whatever the subkeys: the state becomes
`CIPH_K(C ⊕ Mₙ)`. -/
def finRawPPC64LE : Contract isa where
  pre := finalizePPC64LE.pre
  post s s' := bytesAt s'.mem (s.gpr .r5) 16 = ciphAt s.mem (s.gpr .r3) (s.gpr .r4).toNat
    (Spec.Cmac.xor (bytesAt s.mem (s.gpr .r5) 16) (mn s.mem (s.gpr .r3) (s.gpr .r6) (s.gpr .r7).toNat))
  pub := finalizePPC64LE.pub

theorem finalize_raw_wp {s₀ : State} (h0 : finRawPPC64LE.pre s₀) :
    WP isa finalize s₀ fun s' => (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ s'.lr = s₀.lr ∧
      finRawPPC64LE.post s₀ s' := by
  have hp := FPre.of h0
  generalize hW : s₀.gpr .r3 = W at hp
  generalize hSt : s₀.gpr .r5 = St at hp
  generalize hP : s₀.gpr .r6 = P at hp
  generalize hS : s₀.gpr .r8 = S at hp
  generalize hL : (s₀.gpr .r7).toNat = L at hp
  generalize hR : (s₀.gpr .r4).toNat = R at hp
  have hRb : 16 * (R + 1) ≤ 240 := by rcases hp.rounds with h | h | h <;> omega_using [h]
  have sw := hp.scr_wrap
  refine WP.seq (WP.mono (finPre_wp hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (blk_call (name := "vg_aes_encrypt_blocks") Proof.Aes.PPC64LE.encryptBlocks_correct
    Proof.AesCbc.PPC64LE.encryptBlocks_noFrames h₁.pre) fun s₂ c => ?_)
  have slotD : ∀ p ∈ finSaved, ∀ r ∈ [⟨S + BitVec.ofNat 64 2048, 16⟩, ⟨St, 16⟩, ⟨S, 2048⟩],
      Region.Disjoint ⟨S + BitVec.ofNat 64 p.2, 8⟩ r := by
    intro p hp' r hr
    have hb := fin_bound p hp'
    have hsub : Region.Sub ⟨S + BitVec.ofNat 64 p.2, 8⟩ ⟨S, 2176⟩ := Offset.sub_base _ (by omega_using [hb])
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact Offset.disjoint S (by omega_using [hb]) (by omega_using [hb]) (by omega_using [])
    · exact hp.st_scr.symm.sub_left hsub
    · exact Offset.disjoint_base _ (by omega_using [hb]) (by omega_using [hb])
  have hsv : Spill.Saved S (s₀.write .r0 s₀.lr).gpr finSaved s₂.mem :=
    ((Spill.saveMem_saved (by decide) s₀.mem S _).frame h₁.frame fun p hp' r hr =>
      slotD p hp' r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
        rcases hr with rfl | rfl
        · exact .inl rfl
        · exact .inr (.inl rfl))).frame
      c.frame fun p hp' r hr => slotD p hp' r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
        rcases hr with rfl | rfl
        · exact .inr (.inl rfl)
        · exact .inr (.inr rfl))
  have r14₂ : s₂.gpr .r14 = S := by rw [c.saved _ (by decide), h₁.r14]
  have rdwr₂ : s₂.rd ++ s₂.wr = s₀.rd ++ s₀.wr := by rw [c.rd, c.wr, h₁.rd, h₁.wr]
  rw [show finSaved.map (fun (r, d) => Instr.load .d r .r14 d) = Spill.restoreCode .r14 finSaved from rfl]
  refine Spill.restore_ok (b := .r14) (l := finSaved) (by decide) r14₂ (by decide) (by decide)
    (fun p hp' => ?_) hsv fun s₃ r₃ => WP.cons exec_mtlr (wp_nil ⟨fun r hr => ?_, ?_, ?_⟩)
  · have := fin_bound p hp'
    rw [rdwr₂]; exact wr_in (hp.inScr (by omega_using [this]))
  · show s₃.gpr r = _
    have h0 : (s₀.write .r0 s₀.lr).gpr r = s₀.gpr r := by simp [State.write, (preserved_ne r hr).1]
    rw [r₃.gpr_of (r := r) ?_, h0]
    by_cases h14 : r = .r14
    · left; subst h14; decide
    · right; rw [c.saved r hr, h₁.keep r hr h14, h0]
  · show s₃.gpr .r0 = _
    rw [r₃.gpr (.r0, 2064) (by decide)]; simp [State.write]
  · show bytesAt s₃.mem (s₀.gpr .r5) 16 = _
    rw [hW, hR, hSt, hP, hL]
    have sch : bytesAt s₁.mem W (16 * (R + 1)) = bytesAt s₀.mem W (16 * (R + 1)) := by
      rw [Proof.Cmac.bytesAt_frame h₁.frame (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact (hp.key_scr.sub_left (Region.sub_prefix (by omega_using [hRb]))).sub_right (Offset.sub_base _ (by decide))
          · exact hp.key_st.sub_left (Region.sub_prefix (by omega_using [hRb]))) (by omega_using [hRb])]
      exact Proof.Cmac.bytesAt_frame (finMem_frame s₀ S) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hp.key_scr.sub_left (Region.sub_prefix (by omega_using [hRb]))).sub_right (slots_scr S)) (by omega_using [hRb])
    rw [r₃.mem, c.out, cipher_bytes, sch, h₁.st]

theorem finalize_raw_correct (s : State) (hs : finRawPPC64LE.pre s) :
    ∃ t s', Exec isa finalize s t s' ∧ abiPreserved s s' ∧ finRawPPC64LE.post s s' := by
  obtain ⟨t, s', he, hg, hlr, hp⟩ := finalize_raw_wp hs
  exact ⟨t, s', he, ⟨hg, Exec.sp he, hlr⟩, hp⟩

/-- What a call of `vg_cmac_aes_finalize` leaves, whatever the subkeys. -/
structure FRPost (s : State) (K St P S : Addr) (L R : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  saved : ∀ r ∈ preserved, s'.gpr r = s.gpr r
  frame : Frame [⟨St, 16⟩, ⟨S, 2176⟩] s.mem s'.mem
  out : bytesAt s'.mem St 16 = ciphAt s.mem K R (Spec.Cmac.xor (bytesAt s.mem St 16) (mn s.mem K P L))

theorem fin_call_raw {s : State} {K St P S : Addr} {L R : Nat} (h : FArgs s K St P S L R) :
    WP isa Impl.CmacAes.Stream.PPC64LE.finCall s (FRPost s K St P S L R) := by
  have hR := toNat_rounds h.rounds
  have hL := Proof.CmacAes.Stream.PPC64LE.toNat_ofNat (n := L) (by have := h.len; omega_using [this])
  refine WP.call (k := finRawPPC64LE) finalize_raw_correct h.pre h.reads h.writes ?_ finalize_noFrames
  intro s' hrd hwr hsp hf hsaved _ hpost
  refine ⟨hrd, hwr, hsp, hsaved, hf, ?_⟩
  simp only [finRawPPC64LE, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
    callEntry_gpr' s (by decide : Reg.r3 ∉ linkRegs), callEntry_gpr' s (by decide : Reg.r4 ∉ linkRegs),
    callEntry_gpr' s (by decide : Reg.r5 ∉ linkRegs), callEntry_gpr' s (by decide : Reg.r6 ∉ linkRegs),
    callEntry_gpr' s (by decide : Reg.r7 ∉ linkRegs), h.r3, h.r4, h.r5, h.r6, h.r7, hR, hL] at hpost
  exact hpost

end VG.Proof.AesSiv.PPC64LE

end

end

/-!
# AES-SIV on PPC64LE: the calls' arguments, and the CMAC of a string

Untrusted: everything here is checked by Lean. What each call is given
(`uargs`, `fargs`, `cargs`): the key context, a state or counter block in
`W` below 384, the data, and the working space at `W + 384`. `cmacOf`
computes the CMAC of the string with the context's PRF into the state at
`W + st` (`cmacOf_wp`): the code zeroes the state, computes `16 nb`, the
bytes of the whole blocks before the last 1 to 16 (`Spec.Cmac.chainedLen`),
into `r21`, chains the `nb` blocks with `vg_cmac_aes_update` and finalizes
the rest with `vg_cmac_aes_finalize`, from the subkeys in the context
(`Siv.macWith_chained`).
-/

@[expose] public section

namespace VG.Proof.AesSiv.PPC64LE

open VG VG.Impl.AesSiv.PPC64LE
open VG.PPC64LE hiding wp_add wp_addi wp_and wp_ld wp_li wp_lsl wp_lsr wp_lwz wp_std wp_stw wp_sub wp_subi
  wp_xor Upd Mupd
open VG.Proof.ChaCha20Poly1305.PPC64LE (Upd Mupd wp_addi wp_subi wp_li wp_lsr wp_lsl wp_add wp_sub wp_std)
open VG.Proof.AesCcm.PPC64LE (wp_mv)
open VG.Proof.CmacAes.Stream.PPC64LE (UArgs UPost upd_call FArgs)
open VG.Proof.AesCtr.PPC64LE (CtrCall)
open VG.Impl.AesCbc.PPC64LE (mov)
open VG.Spec.Aes (bytesAt)

/-! ## Arithmetic -/

theorem ofNat_lsr4' {n : Nat} (hn : n < 2 ^ 64) : BitVec.ofNat 64 n >>> 4 = BitVec.ofNat 64 (n / 16) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (by omega_arith)]

theorem ofNat_shl4 {n : Nat} (hn : 16 * n < 2 ^ 64) : BitVec.ofNat 64 n <<< 4 = BitVec.ofNat 64 (16 * n) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := n) (by omega_arith),
    Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]
  omega_arith

theorem ofNat_sub' {a b : Nat} (h : b ≤ a) (ha : a < 2 ^ 64) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha,
    Nat.mod_eq_of_lt (a := b) (by omega_arith), Nat.mod_eq_of_lt (a := a - b) (by omega_arith)]
  rw [show 2 ^ 64 - b + a = (a - b) + 2 ^ 64 by omega_arith, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega_arith)]

theorem chainedLen_le (n : Nat) : Spec.Cmac.chainedLen 16 n ≤ n := by
  simp only [Spec.Cmac.chainedLen]; omega_arith

theorem chainedLen_rest (n : Nat) : n - Spec.Cmac.chainedLen 16 n ≤ 16 := by
  simp only [Spec.Cmac.chainedLen]; omega_arith

theorem chainedLen_div (n : Nat) : 16 * (Spec.Cmac.chainedLen 16 n / 16) = Spec.Cmac.chainedLen 16 n := by
  simp only [Spec.Cmac.chainedLen]; omega_arith

theorem chainedLen_pos {n : Nat} (_h : n ≠ 0) : Spec.Cmac.chainedLen 16 n = 16 * ((n - 1) / 16) := by
  simp only [Spec.Cmac.chainedLen]; omega_arith

/-! ## The calls' arguments -/

/-- Data for a call: `len` bytes at `P`, which the code may read, apart from
the working space of the functions called. -/
structure Src (c : Cx) (s : State) (P : Addr) (len : Nat) : Prop where
  rd : Covers [⟨P, len⟩] (s.rd ++ s.wr)
  wrap : P.toNat + len ≤ 2 ^ 64
  qs : (⟨P, len⟩ : Region).Disjoint ⟨c.W + BitVec.ofNat 64 384, 2176⟩

theorem Buf.src {c : Cx} {s : State} {P : Addr} {len : Nat} (h : Buf c s P len) : Src c s P len :=
  ⟨h.rd, h.wrap, h.wd (by decide)⟩

/-- Bytes of `W` below 384 as data. -/
theorem Lay.srcW {c : Cx} (L : Lay c) {s : State} (P : Perm c s) {t k : Nat} (hk : t + k ≤ 384) :
    Src c s (c.W + BitVec.ofNat 64 t) k :=
  ⟨P.wCR (by omega_arith), by rw [L.wrapW (by omega_arith)]; have := L.ww; omega_arith, L.w_w (.inl (by omega_arith)) (by omega_arith) (by decide)⟩

/-- The arguments of `vg_cmac_aes_update`: `K1`'s schedule, the state at
`W + y`, `k` blocks at `Q`, and the working space at `W + 384`. -/
theorem uargs {c : Cx} (L : Lay c) {s : State} (E : Env c s) {y : Nat} (hy : y + 16 ≤ 384) {Q : Addr}
    {k : Nat} (hq : Src c s Q (16 * k)) (hqy : (⟨Q, 16 * k⟩ : Region).Disjoint ⟨c.W + BitVec.ofNat 64 y, 16⟩)
    (hk : 16 * k < 2 ^ 64) (r3 : s.gpr .r3 = c.C) (r4 : s.gpr .r4 = BitVec.ofNat 64 c.R)
    (r5 : s.gpr .r5 = c.W + BitVec.ofNat 64 y) (r6 : s.gpr .r6 = Q) (r7 : s.gpr .r7 = BitVec.ofNat 64 k)
    (r8 : s.gpr .r8 = c.W + BitVec.ofNat 64 384) :
    UArgs s c.C (c.W + BitVec.ofNat 64 y) Q (c.W + BitVec.ofNat 64 384) c.R k where
  r3 := r3
  r4 := r4
  r5 := r5
  r6 := r6
  r7 := r7
  r8 := r8
  rounds := L.rounds
  hn := hk
  wc := L.c0_w' (by decide) (by omega_arith)
  ws := L.c0_w' (by decide) (by decide)
  dc := hqy
  ds := hq.qs
  cs := L.w_w (.inl (by omega_arith)) (by omega_arith) (by decide)
  wrapC := by rw [L.wrapW (by omega_arith)]; have := L.ww; omega_arith
  wrapD := hq.wrap
  wrapS := by rw [L.wrapW (by decide)]; have := L.ww; omega_arith
  reads := Covers.append_left (Covers.cons (E.perm.c0C (by decide)) (Covers.cons hq.rd Covers.nil))
    (Covers.cons (E.perm.wCR (by omega_arith)) (Covers.cons (E.perm.wCR (by decide)) Covers.nil))
  writes := Covers.cons (E.perm.wC (by omega_arith)) (Covers.cons (E.perm.wC (by decide)) Covers.nil)

/-- The arguments of `vg_cmac_aes_finalize`: the key context, the state at
`W + y`, the `k` last bytes at `Q`, and the working space at `W + 384`. -/
theorem fargs {c : Cx} (L : Lay c) {s : State} (E : Env c s) {y : Nat} (hy : y + 16 ≤ 384) {Q : Addr}
    {k : Nat} (hk : k ≤ 16) (hq : Src c s Q k) (hqy : (⟨Q, k⟩ : Region).Disjoint ⟨c.W + BitVec.ofNat 64 y, 16⟩)
    (r3 : s.gpr .r3 = c.C) (r4 : s.gpr .r4 = BitVec.ofNat 64 c.R)
    (r5 : s.gpr .r5 = c.W + BitVec.ofNat 64 y) (r6 : s.gpr .r6 = Q) (r7 : s.gpr .r7 = BitVec.ofNat 64 k)
    (r8 : s.gpr .r8 = c.W + BitVec.ofNat 64 384) :
    FArgs s c.C (c.W + BitVec.ofNat 64 y) Q (c.W + BitVec.ofNat 64 384) k c.R where
  r3 := r3
  r4 := r4
  r5 := r5
  r6 := r6
  r7 := r7
  r8 := r8
  rounds := L.rounds
  len := hk
  kst := L.c0_w' (by decide) (by omega_arith)
  ks := L.c0_w' (by decide) (by decide)
  pst := hqy
  ps := hq.qs
  sts := L.w_w (.inl (by omega_arith)) (by omega_arith) (by decide)
  wrapK := by have := L.cw; omega_arith
  wrapSt := by rw [L.wrapW (by omega_arith)]; have := L.ww; omega_arith
  wrapP := hq.wrap
  wrapS := by rw [L.wrapW (by decide)]; have := L.ww; omega_arith
  reads := Covers.append_left (Covers.cons (E.perm.c0C (by decide)) (Covers.cons hq.rd Covers.nil))
    (Covers.cons (E.perm.wCR (by omega_arith)) (Covers.cons (E.perm.wCR (by decide)) Covers.nil))
  writes := Covers.cons (E.perm.wC (by omega_arith)) (Covers.cons (E.perm.wC (by decide)) Covers.nil)

/-! ## Zeroing a block of `W` -/

theorem zero16_wp {c : Cx} {s : State} (E : Env c s) {d : Nat} (hd : d + 16 ≤ 2576) (hd8 : d % 4 = 0)
    {is : List Instr} {Q : State → Prop}
    (k : ∀ s', PK s s' → (∀ r, r ≠ .r0 → s'.gpr r = s.gpr r) →
      s'.mem = Proof.Cmac.zero2 s.mem (c.W + BitVec.ofNat 64 d) → WP isa (.block is) s' Q) :
    WP isa (.block (Impl.AesCcm.PPC64LE.zero16 d ++ is)) s Q := by
  simp only [Impl.AesCcm.PPC64LE.zero16, List.cons_append, List.nil_append]
  refine wp_li (by decide) fun s₁ u₁ => ?_
  refine wp_std (a := c.W + BitVec.ofNat 64 d) (by decide) ⟨by omega_arith, hd8⟩
    (by rw [u₁.other _ (by decide), E.r14]) (by rw [u₁.wr]; exact E.perm.wW (by omega_arith)) fun s₂ u₂ => ?_
  refine wp_std (a := c.W + BitVec.ofNat 64 d + BitVec.ofNat 64 8) (by decide) ⟨by omega_arith, by omega_arith⟩
    (by rw [u₂.gpr, u₁.other _ (by decide), E.r14, Offset.add_add])
    (by rw [u₂.wr, u₁.wr, Offset.add_add]; exact E.perm.wW (by omega_arith)) fun s₃ u₃ => ?_
  refine k s₃ ((PK.ofUpd u₁).trans ((PK.ofMupd u₂).trans (PK.ofMupd u₃)))
    (fun r hr => by rw [u₃.gpr, u₂.gpr, u₁.other _ hr]) ?_
  rw [u₃.mem, u₂.gpr, u₂.mem, u₁.gpr, u₁.mem, Proof.Cmac.zero2]
  rfl

/-! ## `cmacOf` -/

/-- What the CMAC of a string writes: the state at `W + st` and the working
space of the functions called. -/
abbrev macR (c : Cx) (st : Nat) : List Region := [⟨c.W + BitVec.ofNat 64 st, 16⟩, ⟨c.W + BitVec.ofNat 64 384, 2176⟩]

/-- What `cmacOf` keeps: what every piece does, and the registers holding
the loop's descriptors and the string. -/
structure MacKeep (s s' : State) : Prop where
  pk : PK s s'
  r17 : s'.gpr .r17 = s.gpr .r17
  r18 : s'.gpr .r18 = s.gpr .r18
  r19 : s'.gpr .r19 = s.gpr .r19
  r20 : s'.gpr .r20 = s.gpr .r20

theorem MacKeep.trans {s t u : State} (h₁ : MacKeep s t) (h₂ : MacKeep t u) : MacKeep s u :=
  ⟨h₁.pk.trans h₂.pk, h₂.r17.trans h₁.r17, h₂.r18.trans h₁.r18, h₂.r19.trans h₁.r19, h₂.r20.trans h₁.r20⟩

theorem keep_sub : ∀ r ∈ keepRegs, r ∈ ([.r2, .r14, .r15, .r16, .r17, .r18, .r19, .r20, .r22, .r23, .r24, .r26,
    .r27, .r28, .r29, .r30, .r31] : List Reg) := by decide

theorem MacKeep.ofUpd {s t : State} {d : Reg} {v : BitVec 64} (u : Proof.ChaCha20Poly1305.PPC64LE.Upd s t d v)
    (hd : d ∉ [.r2, .r14, .r15, .r16, .r17, .r18, .r19, .r20, .r22, .r23, .r24, .r26, .r27, .r28, .r29, .r30,
      .r31] := by decide) : MacKeep s t :=
  ⟨PK.ofUpd u (fun h => hd (keep_sub d h)), u.other _ (fun h => hd (by simp [h])),
    u.other _ (fun h => hd (by simp [h])), u.other _ (fun h => hd (by simp [h])),
    u.other _ (fun h => hd (by simp [h]))⟩

theorem MacKeep.ofSaved {s t : State} (hrd : t.rd = s.rd) (hwr : t.wr = s.wr) (hsp : t.sp = s.sp)
    (hs : ∀ r ∈ preserved, t.gpr r = s.gpr r) : MacKeep s t :=
  ⟨PK.ofSaved hrd hwr hsp hs, hs _ (by decide), hs _ (by decide), hs _ (by decide), hs _ (by decide)⟩

/-- `cmacLen`: the state zeroed, and `16 nb` in `r21`. -/
theorem cmacLen_wp {c : Cx} {s : State} (E : Env c s) {st : Nat} (hst : st + 16 ≤ 384) (hst4 : st % 8 = 0)
    {n : Nat} (hn : n < 2 ^ 64) (h20 : s.gpr .r20 = BitVec.ofNat 64 n) :
    WP isa (cmacLen st) s fun s' => MacKeep s s' ∧ s'.gpr .r21 = BitVec.ofNat 64 (Spec.Cmac.chainedLen 16 n) ∧
      s'.mem = Proof.Cmac.zero2 s.mem (c.W + BitVec.ofNat 64 st) := by
  unfold cmacLen
  refine WP.seq (zero16_wp E (d := st) (by omega_arith) (by omega_arith) fun s₁ pk₁ g₁ m₁ => ?_)
  refine wp_li (by decide) fun s₂ u₂ => WP.block_nil ?_
  obtain K₂ : MacKeep s s₂ :=
    ⟨pk₁.trans (PK.ofUpd u₂), by rw [u₂.other _ (by decide), g₁ _ (by decide)],
      by rw [u₂.other _ (by decide), g₁ _ (by decide)], by rw [u₂.other _ (by decide), g₁ _ (by decide)],
      by rw [u₂.other _ (by decide), g₁ _ (by decide)]⟩
  obtain h20₂ : s₂.gpr .r20 = BitVec.ofNat 64 n := by rw [K₂.r20, h20]
  refine WP.ite (decide (n = 0)) (VG.Proof.Gather.PPC64LE.eval_zero h20₂ hn) (fun ht => ?_) (fun hf => ?_)
  · have h0 : n = 0 := by simpa using ht
    subst h0
    exact WP.block_nil ⟨K₂, by rw [u₂.gpr]; rfl, by rw [u₂.mem, m₁]⟩
  · have h0 : n ≠ 0 := by simpa using hf
    refine wp_subi (by decide) (by decide) fun s₃ u₃ => wp_lsr (by decide) fun s₄ u₄ =>
      wp_lsl (by decide) fun s₅ u₅ => WP.block_nil ⟨K₂.trans ((MacKeep.ofUpd u₃).trans ((MacKeep.ofUpd u₄).trans
        (MacKeep.ofUpd u₅))), ?_, by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, m₁]⟩
    rw [u₅.gpr, u₄.gpr, u₃.gpr, h20₂, chainedLen_pos h0]
    rw [show BitVec.ofNat 64 1 = (1 : BitVec 64) from rfl] at *
    rw [show BitVec.ofNat 64 n - 1 = BitVec.ofNat 64 (n - 1) from ofNat_sub' (b := 1) (by omega_arith) hn,
      ofNat_lsr4' (by omega_arith), ofNat_shl4 (by omega_arith)]

/-- `AES-CMAC(K1, S)` into the state at `W + st`, for the string `S` (`n`
bytes at `P`, in `r19` and `r20`). -/
theorem cmacOf_wp {c : Cx} (L : Lay c) {s : State} (E : Env c s) {st : Nat} (hst : st + 16 ≤ 384)
    (hst8 : st % 8 = 0) {P : Addr} {n : Nat} (hP : Buf c s P n) (h19 : s.gpr .r19 = P)
    (h20 : s.gpr .r20 = BitVec.ofNat 64 n) :
    WP isa (cmacOf st) s fun s' => MacKeep s s' ∧ Frame (macR c st) s.mem s'.mem ∧
      bytesAt s'.mem (c.W + BitVec.ofNat 64 st) 16 = Spec.Siv.ctxMac s.mem c.C c.R (bytesAt s.mem P n) := by
  have hn := hP.lt
  obtain hcl := chainedLen_le n
  obtain hcd := chainedLen_div n
  obtain hrest := chainedLen_rest n
  have hRb := L.rb
  unfold cmacOf
  refine WP.seq (WP.mono (cmacLen_wp E hst hst8 hn h20) fun s₁ ⟨K₁, h21₁, m₁⟩ => ?_)
  obtain E₁ := E.of_pk K₁.pk
  obtain h19₁ : s₁.gpr .r19 = P := by rw [K₁.r19, h19]
  obtain h20₁ : s₁.gpr .r20 = BitVec.ofNat 64 n := by rw [K₁.r20, h20]
  -- The update's arguments.
  obtain A₁ : WP isa (.block (cmacArgs₁ st)) s₁ fun s₂ => MacKeep s₁ s₂ ∧ s₂.mem = s₁.mem ∧
      s₂.gpr .r21 = s₁.gpr .r21 ∧
      UArgs s₂ c.C (c.W + BitVec.ofNat 64 st) P (c.W + BitVec.ofNat 64 384) c.R (Spec.Cmac.chainedLen 16 n / 16) := by
    unfold cmacArgs₁ macArgs
    simp only [List.cons_append, List.nil_append]
    refine wp_mv fun t₁ v₁ => wp_mv fun t₂ v₂ => wp_addi (by decide) (by omega_arith) fun t₃ v₃ =>
      wp_addi (by decide) (by decide) fun t₄ v₄ => wp_mv fun t₅ v₅ => wp_lsr (by decide) fun t₆ v₆ =>
      WP.block_nil ?_
    obtain K : MacKeep s₁ t₆ := (MacKeep.ofUpd v₁).trans ((MacKeep.ofUpd v₂).trans ((MacKeep.ofUpd v₃).trans
      ((MacKeep.ofUpd v₄).trans ((MacKeep.ofUpd v₅).trans (MacKeep.ofUpd v₆)))))
    obtain E₆ := E₁.of_pk K.pk
    obtain hq := (hP.take hcl).of_eq (by rw [K.pk.rd, K₁.pk.rd]) (by rw [K.pk.wr, K₁.pk.wr])
    rw [← hcd] at hq
    refine ⟨K, by rw [v₆.mem, v₅.mem, v₄.mem, v₃.mem, v₂.mem, v₁.mem],
      by rw [v₆.other _ (by decide), v₅.other _ (by decide), v₄.other _ (by decide), v₃.other _ (by decide),
        v₂.other _ (by decide), v₁.other _ (by decide)], ?_⟩
    exact uargs L E₆ hst hq.src (hq.wd (d := st) (k := 16) (by omega_arith)) (by omega_arith)
      (by rw [v₆.other _ (by decide), v₅.other _ (by decide), v₄.other _ (by decide), v₃.other _ (by decide),
        v₂.other _ (by decide), v₁.gpr, E₁.r15])
      (by rw [v₆.other _ (by decide), v₅.other _ (by decide), v₄.other _ (by decide), v₃.other _ (by decide),
        v₂.gpr, v₁.other _ (by decide), E₁.r16])
      (by rw [v₆.other _ (by decide), v₅.other _ (by decide), v₄.other _ (by decide), v₃.gpr,
        v₂.other _ (by decide), v₁.other _ (by decide), E₁.r14])
      (by rw [v₆.other _ (by decide), v₅.gpr, v₄.other _ (by decide), v₃.other _ (by decide),
        v₂.other _ (by decide), v₁.other _ (by decide), h19₁])
      (by rw [v₆.gpr, v₅.other _ (by decide), v₄.other _ (by decide), v₃.other _ (by decide),
        v₂.other _ (by decide), v₁.other _ (by decide), h21₁, ofNat_lsr4' (by omega_arith)])
      (by rw [v₆.other _ (by decide), v₅.other _ (by decide), v₄.gpr, v₃.other _ (by decide),
        v₂.other _ (by decide), v₁.other _ (by decide), E₁.r14]; rfl)
  refine WP.seq (WP.mono A₁ fun s₂ ⟨K₂, m₂, h21₂, U⟩ => ?_)
  refine WP.seq (WP.mono (upd_call U) fun s₃ h₃ => ?_)
  obtain K₃ : MacKeep s₂ s₃ := MacKeep.ofSaved h₃.rd h₃.wr h₃.sp h₃.saved
  obtain K₁₃ := K₂.trans K₃
  obtain E₃ := E₁.of_pk K₁₃.pk
  obtain h21₃ : s₃.gpr .r21 = BitVec.ofNat 64 (Spec.Cmac.chainedLen 16 n) := by
    rw [h₃.saved _ (by decide), h21₂, h21₁]
  -- The finalization's arguments.
  obtain hq : Buf c s₃ (P + BitVec.ofNat 64 (Spec.Cmac.chainedLen 16 n)) (n - Spec.Cmac.chainedLen 16 n) :=
    (hP.drop hcl).of_eq (by rw [K₁₃.pk.rd, K₁.pk.rd]) (by rw [K₁₃.pk.wr, K₁.pk.wr])
  obtain A₂ : WP isa (.block (cmacArgs₂ st)) s₃ fun s₄ => MacKeep s₃ s₄ ∧ s₄.mem = s₃.mem ∧
      FArgs s₄ c.C (c.W + BitVec.ofNat 64 st) (P + BitVec.ofNat 64 (Spec.Cmac.chainedLen 16 n))
        (c.W + BitVec.ofNat 64 384) (n - Spec.Cmac.chainedLen 16 n) c.R := by
    unfold cmacArgs₂ macArgs
    simp only [List.cons_append, List.nil_append]
    refine wp_mv fun t₁ v₁ => wp_mv fun t₂ v₂ => wp_addi (by decide) (by omega_arith) fun t₃ v₃ =>
      wp_addi (by decide) (by decide) fun t₄ v₄ => wp_add fun t₅ v₅ => wp_sub fun t₆ v₆ =>
      WP.block_nil ?_
    obtain K : MacKeep s₃ t₆ := (MacKeep.ofUpd v₁).trans ((MacKeep.ofUpd v₂).trans ((MacKeep.ofUpd v₃).trans
      ((MacKeep.ofUpd v₄).trans ((MacKeep.ofUpd v₅).trans (MacKeep.ofUpd v₆)))))
    obtain E₆ := E₃.of_pk K.pk
    obtain hq' := hq.of_eq K.pk.rd K.pk.wr
    refine ⟨K, by rw [v₆.mem, v₅.mem, v₄.mem, v₃.mem, v₂.mem, v₁.mem], ?_⟩
    exact fargs L E₆ hst hrest hq'.src (hq'.wd (by omega_arith))
      (by rw [v₆.other _ (by decide), v₅.other _ (by decide), v₄.other _ (by decide), v₃.other _ (by decide),
        v₂.other _ (by decide), v₁.gpr, E₃.r15])
      (by rw [v₆.other _ (by decide), v₅.other _ (by decide), v₄.other _ (by decide), v₃.other _ (by decide),
        v₂.gpr, v₁.other _ (by decide), E₃.r16])
      (by rw [v₆.other _ (by decide), v₅.other _ (by decide), v₄.other _ (by decide), v₃.gpr,
        v₂.other _ (by decide), v₁.other _ (by decide), E₃.r14])
      (by simp (disch := decide) only [v₆.other, v₅.gpr, v₄.other, v₃.other, v₂.other, v₁.other, K₁₃.r19, h19₁,
        h21₃])
      (by
        simp (disch := decide) only [v₆.gpr, v₅.other, v₄.other, v₃.other, v₂.other, v₁.other, K₁₃.r20, h20₁, h21₃]
        exact ofNat_sub' hcl hn)
      (by rw [v₆.other _ (by decide), v₅.other _ (by decide), v₄.gpr, v₃.other _ (by decide),
        v₂.other _ (by decide), v₁.other _ (by decide), E₃.r14]; rfl)
  refine WP.seq (WP.mono A₂ fun s₄ ⟨K₄, m₄, F⟩ => ?_)
  refine WP.mono (fin_call_raw F) fun s₅ h₅ => ?_
  obtain K₅ : MacKeep s₄ s₅ := MacKeep.ofSaved h₅.rd h₅.wr h₅.sp h₅.saved
  refine ⟨K₁.trans (K₁₃.trans (K₄.trans K₅)), ?_, ?_⟩
  -- The memory: what each step writes.
  obtain f₁ : Frame (macR c st) s.mem s₁.mem := by
    rw [m₁]; exact (Proof.Cmac.frame_store2 _ _ _).mono (by simp)
  have f₃ : Frame (macR c st) s₂.mem s₃.mem := h₃.frame
  have f₅ : Frame (macR c st) s₄.mem s₅.mem := h₅.frame
  obtain f₁₃ : Frame (macR c st) s.mem s₃.mem := f₁.trans (by rw [← m₂]; exact f₃)
  · exact f₁₃.trans (by rw [← m₄]; exact f₅)
  -- What the calls read is as on entry.
  obtain f₁ : Frame (macR c st) s.mem s₁.mem := by
    rw [m₁]; exact (Proof.Cmac.frame_store2 _ _ _).mono (by simp)
  obtain f₁₃ : Frame (macR c st) s.mem s₃.mem := f₁.trans (by rw [← m₂]; exact h₃.frame)
  obtain dc : ∀ r ∈ macR c st, (⟨c.C, 512⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact L.c0_w' (by decide) (by omega_arith)
    · exact L.c0_w' (by decide) (by decide)
  obtain dp : ∀ r ∈ macR c st, (⟨P, n⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hP.wd (by omega_arith)
    · exact hP.wd (by decide)
  have cK {d k : Nat} (hd : d + k ≤ 512) {m' : Mem} (hf : Frame (macR c st) s.mem m') :
      bytesAt m' (c.C + BitVec.ofNat 64 d) k = bytesAt s.mem (c.C + BitVec.ofNat 64 d) k :=
    Proof.Cmac.bytesAt_frame hf (fun r hr => (dc r hr).sub_left (Lay.cSub hd)) (by omega_arith)
  have cP {d k : Nat} (hd : d + k ≤ n) {m' : Mem} (hf : Frame (macR c st) s.mem m') :
      bytesAt m' (P + BitVec.ofNat 64 d) k = bytesAt s.mem (P + BitVec.ofNat 64 d) k :=
    Proof.Cmac.bytesAt_frame hf (fun r hr => (dp r hr).sub_left (Offset.sub_base _ hd)) (by omega_arith)
  obtain k0 : ∀ a : Addr, a + BitVec.ofNat 64 0 = a := fun a => BitVec.add_zero a
  obtain sch₁ := cK (d := 0) (k := 16 * (c.R + 1)) (by omega_arith) f₁
  obtain sch₃ := cK (d := 0) (k := 16 * (c.R + 1)) (by omega_arith) f₁₃
  obtain k1 := cK (d := 240) (k := 16) (by decide) f₁₃
  obtain k2 := cK (d := 256) (k := 16) (by decide) f₁₃
  obtain pre₁ := cP (d := 0) (k := Spec.Cmac.chainedLen 16 n) (by omega_arith) f₁
  obtain rest₃ := cP (d := Spec.Cmac.chainedLen 16 n) (k := n - Spec.Cmac.chainedLen 16 n) (by omega_arith) f₁₃
  rw [k0] at sch₁ sch₃ pre₁
  obtain hz : bytesAt s₁.mem (c.W + BitVec.ofNat 64 st) 16 = Spec.Cmac.zeros 16 := by
    rw [m₁, Proof.Cmac.zero2_bytes]
  obtain hS : (bytesAt s.mem P n).length = n := Proof.Cmac.bytesAt_length _ _ _
  obtain hsplit : n = Spec.Cmac.chainedLen 16 n + (n - Spec.Cmac.chainedLen 16 n) := by omega_arith
  obtain tk : (bytesAt s.mem P n).take (Spec.Cmac.chainedLen 16 n) =
      bytesAt s.mem P (Spec.Cmac.chainedLen 16 n) := by
    have := take_bytesAt s.mem P (a := Spec.Cmac.chainedLen 16 n) (b := n - Spec.Cmac.chainedLen 16 n)
    rwa [← hsplit] at this
  obtain dr : (bytesAt s.mem P n).drop (Spec.Cmac.chainedLen 16 n) =
      bytesAt s.mem (P + BitVec.ofNat 64 (Spec.Cmac.chainedLen 16 n)) (n - Spec.Cmac.chainedLen 16 n) := by
    have := drop_bytesAt s.mem P (a := Spec.Cmac.chainedLen 16 n) (b := n - Spec.Cmac.chainedLen 16 n)
    rwa [← hsplit] at this
  have out₃ := h₃.out
  have out₅ := h₅.out
  rw [m₄] at out₅
  rw [m₂] at out₃
  rw [out₅, out₃, Proof.CmacAes.PPC64LE.mn, Proof.CmacAes.PPC64LE.ciphAt, sch₃, k1, k2, rest₃, sch₁, hz, Proof.Cmac.Stream.blocksAt_eq, hcd,
    pre₁, Spec.Siv.ctxMac, Spec.Siv.schedCiph, Siv.macWith_chained, hS, tk, dr]
  rfl

end VG.Proof.AesSiv.PPC64LE
