module

public import VerifiedGarbage.Spec.Dsa.Derive
public import VerifiedGarbage.Proof.Dsa.Contract
public import VerifiedGarbage.Proof.Framework.X86.RelCT
public import VerifiedGarbage.Proof.Dsa.ProbablePrimeContract
public import VerifiedGarbage.Proof.Framework.X86.CallWith
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Dsa.X86.Generation.Env
public import VerifiedGarbage.Impl.Dsa.X86.Generation
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Dsa.X86.Generation.Words
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Block
import VerifiedGarbage.Proof.Pbkdf2.Stream.X86.Common
import VerifiedGarbage.Proof.Hmac.Common
import VerifiedGarbage.Proof.Hmac.Generic.Common
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.X86.Wp
public import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Impl.Pbkdf2.Md.X86
public import VerifiedGarbage.Proof.Mont.Words
public import VerifiedGarbage.Spec.Sha256
public import VerifiedGarbage.TCB.X86.Isa

/-! ### `Dsa.X86.Generation.TestPre`, which this module and modules that import it used -/

section

/-! ### `Dsa.X86.Generation.Hash`, which this module and modules that import it used -/

section

/-! # A message of one hash value's length, hashed by the compression function

Parameter generation hashes seeds of `N` bytes, as many as the hash value
has (SHA-1's 20, SHA-256's 32): one block, the seed and its padding, after
the initial value, compressed once by a verified compression function. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation
open VG.Impl.Pbkdf2.Md.X86 (Hash storeW)
open VG.Proof.MdStream (Md)
open VG.Proof.Pbkdf2.Md.X86 (MdOk CmpArgs storeW_ok cmp_ok OutOk inReg)
open VG.X86.Wp (Upd wp_mov wp_addi)
open VG.Proof.Pbkdf2.Stream.X86 (stk After setWidth_add toNat_add_ofNat)
open VG.Proof.Hmac.Common (bytesAt_length bytesAt_writeBytes_sep)
open VG.WriteBytes (writeBytes writeBytes_frame)

/-- What hashing needs of a hash function's code and its initial value:
the proofs' facts about the code (`MdOk`), an initial value whose bytes
are the `md`'s initial hash value, a length field of eight bytes,
big-endian, and a digest of the hash value's length. -/
structure HashOk (H : Hash) (iv : List (BitVec 32)) where
  ok : MdOk H
  ivLen : 4 * iv.length = H.N
  ivVal : ∀ m p, Spec.Sha256.bytesAt m p H.N = ivBytes iv → ok.md.stateAt m p = ok.iv
  lenB : ok.md.lenBytes H.N = (List.range 8).map fun i => BitVec.ofNat 8 ((8 * H.N) >>> (8 * (7 - i)))
  B : H.B = 64
  L : H.L = 8
  DN : H.D = H.N

theorem ivBytes_length (iv : List (BitVec 32)) : (ivBytes iv).length = 4 * iv.length := by
  induction iv with
  | nil => rfl
  | cons _ _ ih =>
    simp only [ivBytes, List.flatMap_cons, List.length_append, List.length_map, List.length_range,
      List.length_cons] at ih ⊢
    omega_arith

theorem padBytes_length {n : Nat} (h : n + 9 ≤ 64) : (padBytes n).length = 64 - n := by
  simp only [padBytes, List.length_append, List.length_singleton, List.length_replicate, List.length_map,
    List.length_range]
  omega_arith

theorem contains_start (p : Addr) {n k : Nat} (h : n ≤ k) : (⟨p, k⟩ : Region).Contains p n := by
  simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega_arith

/-- The three writes of a hash, within its regions. -/
theorem frame_join {A B C D A' : Region} {m₁ m₂ m₃ m₄ : Mem} (f₁ : Frame [A] m₁ m₂)
    (f₂ : Frame ([A', B] ++ [D]) m₂ m₃) (f₃ : Frame [C] m₃ m₄) (h : Region.Sub A' A) :
    Frame [A, B, C, D] m₁ m₄ := by
  refine (f₁.mono ?_).trans ((f₂.sub ?_).trans (f₃.mono ?_))
  · intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact .head _
  · intro r hr
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨A, .head _, h⟩
    · exact ⟨_, .tail _ (.head _), fun _ h => h⟩
    · exact ⟨_, .tail _ (.tail _ (.tail _ (.head _))), fun _ h => h⟩
  · intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact .tail _ (.tail _ (.head _))

section
variable {H : Hash} {iv : List (BitVec 32)} (F : HashOk H iv)
include F

theorem HashOk.N_le : H.N + 12 ≤ 64 := by
  have := F.ok.sizes.DL; have := F.B; have := F.L; have := F.DN; omega_arith

theorem HashOk.N4 : H.N % 4 = 0 := by
  have := F.ok.sizes.N; omega_arith

/-- The block before the compression: the initial value, the padding after
the message, the block's address in `eax` and the scratch space's in `ebp`. -/
theorem prep_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size)
    (hsz : sHScr ≤ size) {Q : State → Prop}
    (k : ∀ t, t.gpr .ebx = s.gpr .edi + BitVec.ofNat 32 sState →
      t.gpr .eax = s.gpr .edi + BitVec.ofNat 32 sState + BitVec.ofNat 32 H.N →
      t.gpr .ebp = s.gpr .edi + BitVec.ofNat 32 sHScr →
      (∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .ecx → r ≠ .ebp → t.gpr r = s.gpr r) → t.rd = s.rd → t.wr = s.wr →
      t.mem = writeBytes (writeBytes s.mem (off base sState) (ivBytes iv))
        (off base sState + BitVec.ofNat 64 (H.N + H.N)) (padBytes H.N) → Q t) :
    WP isa (.block (scr .ebx sState ++ ivStore iv ++
      Impl.Pbkdf2.Md.X86.storeW .ebx (H.N + H.N) (padBytes H.N) ((64 - H.N) / 4) ++
      ([.mov .eax (.reg .ebx), .alu .add .eax (.imm (BitVec.ofNat 32 H.N))] : List Instr) ++ scr .ebp sHScr)) s Q := by
  obtain nl := F.N_le; have n4 := F.N4; have ivl := F.ivLen
  have nw := hs.nowrap
  obtain hsn : sState + H.N + 64 ≤ sHScr := by simp only [sState, sHScr]; omega_arith
  obtain yNat := Scr.toNat_add hs (d := sState) (by simp only [sState, sHScr] at hsz ⊢; omega_arith)
  obtain yW := Scr.wide hs (d := sState) (by simp only [sState, sHScr] at hsz ⊢; omega_arith)
  simp only [List.append_assoc]
  refine scr_ok fun s₁ e₁ g₁ m₁ rd₁ wr₁ _ => ?_
  obtain cov : ∀ d n, sState ≤ d → d + n ≤ sState + H.N + 64 →
      ∀ j, j + 4 ≤ n → InRegions s₁.wr (addr (s.gpr .edi + BitVec.ofNat 32 sState) (d - sState + j)) 4 := by
    intro d n h₁ h₂ j hj
    rw [addr_eq (by omega_arith), yW, Offset.add_add, wr₁]
    exact hs.write (d := sState + (d - sState + j)) (n := 4) (by omega_arith)
  unfold ivStore
  refine storeW_ok (by decide) iv.length _ s₁ _ (by rw [ivBytes_length]) e₁ (by omega_arith)
    (fun j hj => by simpa using cov sState (4 * iv.length) (Nat.le_refl _) (by omega_arith) (4 * j) (by omega_arith))
    fun s₂ g₂ rd₂ wr₂ m₂ => ?_
  refine storeW_ok (by decide) ((64 - H.N) / 4) _ s₂ _ (by rw [padBytes_length (by omega_arith)]; omega_arith)
    (by rw [g₂ _ (by decide), e₁]) (by omega_arith)
    (fun j hj => by
      rw [wr₂]
      have := cov (sState + (H.N + H.N)) (64 - H.N) (by omega_arith) (by omega_arith) (4 * j) (by omega_arith)
      rwa [show sState + (H.N + H.N) - sState + 4 * j = H.N + H.N + 4 * j by omega_arith] at this)
    fun s₃ g₃ rd₃ wr₃ m₃ => ?_
  simp only [List.cons_append, List.nil_append]
  refine wp_mov fun s₄ u₄ => wp_addi fun s₅ u₅ => ?_
  refine scr_ok fun s₆ e₆ g₆ m₆ rd₆ wr₆ _ => WP.block_nil (k s₆ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
  · rw [g₆ _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), g₃ _ (by decide),
      g₂ _ (by decide), e₁]
  · rw [g₆ _ (by decide), u₅.gpr, u₄.gpr, g₃ _ (by decide), g₂ _ (by decide), e₁]
  · rw [e₆, u₅.other _ (by decide), u₄.other _ (by decide), g₃ _ (by decide), g₂ _ (by decide),
      g₁ _ (by decide)]
  · intro r a b c d
    rw [g₆ r d, u₅.other r a, u₄.other r a, g₃ r c, g₂ r c, g₁ r b]
  · rw [rd₆, u₅.rd, u₄.rd, rd₃, rd₂, rd₁]
  · rw [wr₆, u₅.wr, u₄.wr, wr₃, wr₂, wr₁]
  · rw [m₆, u₅.mem, u₄.mem, m₃, m₂, m₁, yW, Nat.mul_comm 4 ((64 - H.N) / 4),
      Nat.div_mul_cancel (by omega_arith), ← ivBytes_length,
      List.take_of_length_le (Nat.le_refl _), List.take_of_length_le (by rw [padBytes_length (by omega_arith)]),
      BitVec.add_zero]

/-- The bytes of the block after the hash value: the message, then the
padding. -/
theorem block_bytes {m : Mem} {Y : Addr} {k : Nat} (hk : k < 64) :
    writeBytes (writeBytes m Y (ivBytes iv)) (Y + BitVec.ofNat 64 (H.N + H.N)) (padBytes H.N)
        (Y + BitVec.ofNat 64 H.N + BitVec.ofNat 64 k) =
      (Spec.Sha256.bytesAt m (Y + BitVec.ofNat 64 H.N) H.N ++ padBytes H.N).getD k 0 := by
  obtain nl := F.N_le; have ivl := F.ivLen
  obtain pl := padBytes_length (n := H.N) (by omega_arith)
  obtain il := ivBytes_length iv
  obtain ml : (Spec.Sha256.bytesAt m (Y + BitVec.ofNat 64 H.N) H.N).length = H.N := by
    simp only [Spec.Sha256.bytesAt, List.length_map, List.length_range]
  rw [Offset.add_add]
  obtain d1 := Offset.sub_toNat' Y (d := H.N + H.N) (e := H.N + k) (by omega_arith) (by omega_arith)
  obtain d2 := Mem.sub_ofNat_toNat Y (show H.N + k < 2 ^ 64 by omega_arith)
  simp only [writeBytes, d1, d2, List.getD_eq_getElem?_getD]
  by_cases hN : H.N ≤ k
  · have c1 : H.N + H.N ≤ H.N + k := by omega_arith
    obtain c2 : H.N + k - (H.N + H.N) < (padBytes H.N).length := by rw [pl]; omega_arith
    simp only [c1, ↓reduceIte, c2]
    rw [List.getElem?_append_right (by rw [ml]; exact hN), ml]
    congr 2
    omega_arith
  · have c1 : ¬ H.N + H.N ≤ H.N + k := by omega_arith
    obtain c2 : ¬ 2 ^ 64 + (H.N + k) - (H.N + H.N) < (padBytes H.N).length := by rw [pl]; omega_arith
    obtain c3 : ¬ H.N + k < (ivBytes iv).length := by rw [il]; omega_arith
    simp only [c1, ↓reduceIte, c2, c3]
    rw [List.getElem?_append_left (by rw [ml]; omega_arith)]
    simp only [Spec.Sha256.bytesAt, List.getElem?_map, List.getElem?_range (show k < H.N by omega_arith),
      Option.map_some, Option.getD_some]
    rw [Offset.add_add]

omit F in
/-- The registers `hash` keeps are the compression function's callee-saved ones (stated here, so
that the cases are split in no context). -/
private theorem calleeSaved_of_ne (r : Reg) (a : r ≠ .eax) (b : r ≠ .ebx) (c : r ≠ .ecx) (d : r ≠ .edx)
    (e : r ≠ .ebp) : r ∈ calleeSaved := by
  cases r <;> simp_all [calleeSaved]

theorem hash_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size)
    {dst : Nat} (hsz : sHScr + H.so ≤ size) (hsC : sHScr < size) (hdst : dst + H.N ≤ size)
    (hsepS : sState + H.N + 64 ≤ dst ∨ dst + H.N ≤ sState)
    (hsepC : dst + H.N ≤ sHScr ∨ sHScr + H.so ≤ dst)
    (h48 : 48 ≤ (s.gpr .esp).toNat) (hstk : (stk s).Disjoint ⟨base, size⟩) :
    WP isa (Impl.Dsa.X86.Generation.hash H iv H.N dst) s fun t =>
      Spec.Sha256.bytesAt t.mem (off base dst) H.N =
        F.ok.hH.SH.H.hash (Spec.Sha256.bytesAt s.mem (off base (sState + H.N)) H.N) ∧
      Frame [⟨off base sState, H.N + 64⟩, ⟨off base sHScr, H.so⟩, ⟨off base dst, H.N⟩, stk s] s.mem t.mem ∧
      (∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .ecx → r ≠ .edx → r ≠ .ebp → t.gpr r = s.gpr r) ∧
      t.rd = s.rd ∧ t.wr = s.wr := by
  obtain nl := F.N_le; have n4 := F.N4; have ivl := F.ivLen
  obtain hB := F.B; have hL := F.L; have hD := F.DN
  have nw := hs.nowrap
  obtain hso : sState + H.N + 64 ≤ sHScr := by simp only [sState, sHScr]; omega_arith
  obtain hsS : sState < size := by simp only [sState, sHScr] at hsz hso ⊢; omega_arith
  let Y := off base sState
  obtain yNat := Scr.toNat_add hs hsS
  obtain yW := Scr.wide hs hsS
  obtain cNat := Scr.toNat_add hs hsC
  obtain cW := Scr.wide hs hsC
  unfold Impl.Dsa.X86.Generation.hash
  simp only [seqs]
  refine WP.seq (prep_ok F hs (by omega_arith) fun t eb ea ep g rd wr m => ?_)
  obtain tsp : t.gpr .esp = s.gpr .esp := g _ (by decide) (by decide) (by decide) (by decide)
  obtain tdi : t.gpr .edi = s.gpr .edi := g _ (by decide) (by decide) (by decide) (by decide)
  obtain cargs : CmpArgs H.N H.B H.so t (s.gpr .edi + BitVec.ofNat 32 sState) (s.gpr .edi + BitVec.ofNat 32 sHScr) :=
    { ebx := eb, eax := ea, ebp := ep, sp48 := by rw [tsp]; exact h48
      cst := by rw [yW, wr]; exact Scr.covers hs (by rw [hB]; omega_arith)
      csc := by rw [cW, wr]; exact Scr.covers hs (by omega_arith)
      st_sc := by rw [yW, cW]; exact Offset.disjoint base (by rw [hB]; omega_arith) (by omega_arith) (by omega_arith)
      b_st := by
        rw [stk, tsp, yW]
        exact hstk.sub_right (Offset.sub_base base (by rw [hB]; omega_arith))
      b_sc := by
        rw [stk, tsp, cW]
        exact hstk.sub_right (Offset.sub_base base (by omega_arith))
      nst := by rw [yNat, hB]; omega_arith
      nsc := by rw [cNat]; omega_arith }
  refine WP.seq (cmp_ok F.ok.comp (by rw [hB]; decide) cargs fun u au cu => ?_)
  rw [yW] at cu
  obtain udi : u.gpr .edi = s.gpr .edi := (au.cs .edi (by decide)).trans tdi
  obtain usp : u.gpr .esp = s.gpr .esp := (au.cs .esp (by decide)).trans tsp
  simp only [List.append_assoc]
  refine scr_ok fun v ev gv mv rdv wrv _ => scr_ok fun w ew gw mw rdw wrw _ => ?_
  have npos := F.ok.sizes.N.1
  obtain hdN : dst < size := by omega_arith
  obtain wbx : w.gpr .ebx = s.gpr .edi + BitVec.ofNat 32 sState := by
    rw [gw _ (by decide), ev, udi]
  obtain wax : w.gpr .eax = s.gpr .edi + BitVec.ofNat 32 dst := by
    rw [ew, gv _ (by decide), udi]
  obtain dW := Scr.wide hs hdN
  obtain dNat := Scr.toNat_add hs hdN
  refine WP.mono (F.ok.out w (by rw [wbx, yNat]; omega_arith) (by rw [wax, dNat]; omega_arith) ?_ ?_ ?_)
    fun x ⟨gx, rdx, wrx, mx⟩ => ?_
  · rw [wbx, yW, rdw, wrw, rdv, wrv, au.rd, au.wr, rd, wr]
    exact hs.read (by omega_arith)
  · rw [wax, dW, wrw, wrv, au.wr, wr]; exact hs.write (by omega_arith)
  · rw [wbx, wax, yW, dW]; exact Offset.disjoint base (by omega_arith) (by omega_arith) (by omega_arith)
  rw [wbx, wax, yW, dW, mw, mv] at mx
  -- The value.
  obtain msgEq : Spec.Sha256.bytesAt s.mem (off base (sState + H.N)) H.N =
      Spec.Sha256.bytesAt s.mem (Y + BitVec.ofNat 64 H.N) H.N := by
    simp only [Y, off, Offset.add_add]
  obtain pl := padBytes_length (n := H.N) (by omega_arith)
  obtain ivAt : F.ok.md.stateAt t.mem Y = F.ok.iv := by
    apply F.ivVal
    rw [m, bytesAt_writeBytes_sep _ _ (Offset.sep_base Y (by omega_arith) (by omega_arith)) (by omega_arith),
      VG.Proof.Hmac.Generic.Common.bytesAt_writeBytes_self' (by rw [ivBytes_length]; omega_arith) (by omega_arith)]
  obtain blk : F.ok.md.blockAt t.mem (Y + BitVec.ofNat 64 H.N) =
      F.ok.md.parse fun k => (Spec.Sha256.bytesAt s.mem (Y + BitVec.ofNat 64 H.N) H.N ++ padBytes H.N).getD k 0 := by
    simp only [Md.blockAt]
    refine F.ok.md.parse_congr fun k hk => ?_
    rw [m, block_bytes F (by rw [← hB]; exact hk)]
  obtain ml : (Spec.Sha256.bytesAt s.mem (Y + BitVec.ofNat 64 H.N) H.N).length = H.N := by
    simp only [Spec.Sha256.bytesAt, List.length_map, List.length_range]
  obtain padEq : ∀ msg : List Byte, msg.length = H.N →
      VG.Proof.MdStream.Md.rest H.B msg ++ [0x80] ++ List.replicate (H.B - H.L - 1 - H.N % H.B) 0 ++
        F.ok.md.lenBytes H.N = msg ++ padBytes H.N := by
    intro msg hm
    rw [F.lenB, hB, hL]
    simp only [VG.Proof.MdStream.Md.rest, hm, padBytes, List.append_assoc]
    rw [Nat.div_eq_of_lt (by omega_arith), Nat.mul_zero, List.drop_zero, Nat.mod_eq_of_lt (by omega_arith)]
  obtain hashEq : F.ok.hH.SH.H.hash (Spec.Sha256.bytesAt s.mem (Y + BitVec.ofNat 64 H.N) H.N) =
      F.ok.md.digest (F.ok.md.compress F.ok.iv
        (F.ok.md.parse fun k => (Spec.Sha256.bytesAt s.mem (Y + BitVec.ofNat 64 H.N) H.N ++ padBytes H.N).getD k 0)) := by
    rw [F.ok.link.hash, Md.hash_one F.ok.md (by rw [hB]; decide) (by rw [ml, hB, hL]; omega_arith), ml,
      Nat.div_eq_of_lt (by rw [hB]; omega_arith), Md.compressList_zero, padEq _ ml, hD,
      List.take_of_length_le (by rw [F.ok.md.digest_length])]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [mx, VG.Proof.Hmac.Generic.Common.bytesAt_writeBytes_self' (F.ok.md.digest_length _) (by omega_arith), cu, ivAt, blk,
      msgEq, hashEq]
  · have f₁ : Frame [⟨Y, H.N + 64⟩] s.mem t.mem := by
      rw [m]
      exact (writeBytes_frame _ _ _ (by rw [ivBytes_length]; exact contains_start _ (by omega_arith))).trans
        (writeBytes_frame _ _ _ (by rw [pl]; exact Offset.contains_base Y (by omega_arith) (by omega_arith)))
    have f₂ := au.frame
    rw [yW, cW, stk, tsp] at f₂
    obtain f₃ : Frame [⟨off base dst, H.N⟩] u.mem x.mem := by
      rw [mx]; exact writeBytes_frame _ _ _ (by rw [F.ok.md.digest_length]; exact contains_start _ (by omega_arith))
    obtain s₂ : Region.Sub ⟨off base sState, H.N⟩ ⟨off base sState, H.N + 64⟩ := Region.sub_prefix (by omega_arith)
    exact frame_join f₁ f₂ f₃ s₂

  · intro r a b c d e
    rw [gx r c d, gw r a, gv r b, au.cs r ?_, g r a b c e]
    exact calleeSaved_of_ne r a b c d e
  · rw [rdx, rdw, rdv, au.rd, rd]
  · rw [wrx, wrw, wrv, au.wr, wr]

end

end VG.Proof.Dsa.X86.Generation

end

end

/-! # A probable-prime test's call meets the test's contract -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86/Generation/TestArgs.lean`, which only this module imported.
section

/-! # The arguments of a probable-prime test

The working space at `sPP`, its 64-bit words, the witnesses left (from
`fUsed` on) and the word `fUsedOut` for the octets the test reads. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation
open VG.Impl.Mont.X86 (sc)

/-- The witnesses left: from `used` on, or the start of the tape once none
is left (so that the pointer stays within the tape). -/
def randPtr (W : BitVec 32) (witLen used : Nat) : BitVec 32 :=
  if witLen - used = 0 then W else W + BitVec.ofNat 32 used

/-- The registers a test's call pushes: `ws`, `ws_len`, `rand`, `rand_len`
and `used`, from the state words. -/
structure TestArgs (base : Addr) (W : BitVec 32) (witLen used : Nat) (s t : State) : Prop where
  eax : t.gpr .eax = s.gpr .edi + BitVec.ofNat 32 sPP
  ecx : t.gpr .ecx = BitVec.ofNat 32 ppWords
  edx : t.gpr .edx = randPtr W witLen used
  ebx : t.gpr .ebx = BitVec.ofNat 32 (witLen - used)
  ebp : t.gpr .ebp = s.gpr .edi + BitVec.ofNat 32 fUsedOut
  other : ∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .ecx → r ≠ .edx → r ≠ .ebp → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  syms : t.syms = s.syms

/-- After the test's first block: the cursor's pointer and the octets left,
and whether none are. -/
structure TestHead (base : Addr) (W : BitVec 32) (witLen used : Nat) (s t : State) : Prop where
  zf : t.zf = some (decide (witLen - used = 0))
  edx : t.gpr .edx = W + BitVec.ofNat 32 used
  ebx : t.gpr .ebx = BitVec.ofNat 32 (witLen - used)
  other : ∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .ecx → r ≠ .edx → r ≠ .ebp → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  syms : t.syms = s.syms

theorem testHead_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) (hsz : sPP ≤ size)
    {W : BitVec 32} {witLen used : Nat} (hW : s.mem.readW (off base fWit) 32 = W)
    (hWL : s.mem.readW (off base fWitLen) 32 = BitVec.ofNat 32 witLen)
    (hU : s.mem.readW (off base fUsed) 32 = BitVec.ofNat 32 used) (hu : used ≤ witLen)
    (hwl : witLen < 2 ^ 32) :
    WP isa (.block [.mov .ecx (.mem (sc fUsed)), .mov .edx (.mem (sc fWit)), .alu .add .edx (.reg .ecx),
        .mov .ebx (.mem (sc fWitLen)), .alu .sub .ebx (.reg .ecx)]) s (TestHead base W witLen used s) := by
  obtain szs : fWitLen + 4 ≤ size ∧ fUsed + 4 ≤ size ∧ fWit + 4 ≤ size := by
    simp only [fWitLen, fUsed, fWit, hdr, sPP] at hsz ⊢; omega_using [hsz]
  refine ld_ok hs (by omega_using [szs]) fun s₁ u₁ => ld_ok (Scr.of_eq hs (u₁.other _ (by decide))
    (u₁.other _ (by decide)) u₁.wr) (by omega_using [szs]) fun s₂ u₂ => wp_add fun s₃ u₃ _ => ?_
  obtain edi₃ : s₃.gpr .edi = s.gpr .edi := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
  refine ld_ok (Scr.of_eq hs edi₃
    (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)])
    (by rw [u₃.wr, u₂.wr, u₁.wr])) (by omega_using [szs]) fun s₄ u₄ => wp_sub fun s₅ u₅ z₅ => WP.block_nil ?_
  obtain c₂ : s₂.gpr .ecx = BitVec.ofNat 32 used := by rw [u₂.other _ (by decide), u₁.gpr, hU]
  obtain d₂ : s₂.gpr .edx = W := by rw [u₂.gpr, u₁.mem, hW]
  obtain b₅ : s₅.gpr .ebx = BitVec.ofNat 32 (witLen - used) := by
    rw [u₅.gpr, u₄.gpr, u₄.other _ (by decide), u₃.other _ (by decide), c₂, u₃.mem, u₂.mem, u₁.mem, hWL,
      BitVec.ofNat_sub_ofNat_of_le _ _ (by omega_using [hu, hwl]) hu]
  refine ⟨?_, ?_, b₅, ?_, ?_, ?_, ?_, ?_⟩
  · rw [z₅, ← u₅.gpr, b₅, ofNat_beq_zero (by omega_using [hwl])]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, d₂, c₂]
  · intro r a b c d e
    rw [u₅.other r b, u₄.other r b, u₃.other r d, u₂.other r d, u₁.other r c]
  · rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  · rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  · rw [u₅.syms, u₄.syms, u₃.syms, u₂.syms, u₁.syms]

/-- The cursor's pointer, the start of the tape if none are left, and the
other arguments. -/
theorem testMid_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) (hsz : sPP ≤ size)
    {W : BitVec 32} {witLen used : Nat} (hW : s.mem.readW (off base fWit) 32 = W) {t : State}
    (H : TestHead base W witLen used s t) :
    WP isa (.seq (.ite .e (.block [.mov .edx (.mem (sc fWit))]) (.block []))
      (.block (scr .eax sPP ++ ([.mov .ecx (.imm (BitVec.ofNat 32 ppWords))] : List Instr) ++ scr .ebp fUsedOut))) t
      (TestArgs base W witLen used s) := by
  obtain szs : fWit + 4 ≤ size := by simp only [fWit, hdr, sPP] at hsz ⊢; omega_using [hsz]
  obtain edi₅ : t.gpr .edi = s.gpr .edi := H.other _ (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain sp₅ : t.gpr .esp = s.gpr .esp := H.other _ (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain hs₅ : Scr t base size := Scr.of_eq hs edi₅ sp₅ H.wr
  obtain tail : ∀ x : State, x.gpr .edi = s.gpr .edi → x.gpr .edx = randPtr W witLen used →
      x.gpr .ebx = BitVec.ofNat 32 (witLen - used) →
      (∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .ecx → r ≠ .edx → r ≠ .ebp → x.gpr r = s.gpr r) →
      x.mem = s.mem → x.rd = s.rd → x.wr = s.wr → x.syms = s.syms →
      WP isa (.block (scr .eax sPP ++ ([.mov .ecx (.imm (BitVec.ofNat 32 ppWords))] : List Instr) ++ scr .ebp fUsedOut)) x
        (TestArgs base W witLen used s) := by
    intro x xd xdx xbx xo xm xrd xwr xsy
    simp only [List.append_assoc]
    refine scr_ok fun s₆ e₆ g₆ m₆ rd₆ wr₆ sy₆ => wp_movi fun s₇ u₇ => scr_ok fun s₈ e₈ g₈ m₈ rd₈ wr₈ sy₈ => ?_
    refine WP.block_nil ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [g₈ _ (by decide), u₇.other _ (by decide), e₆, xd]
    · rw [g₈ _ (by decide), u₇.gpr]
    · rw [g₈ _ (by decide), u₇.other _ (by decide), g₆ _ (by decide), xdx]
    · rw [g₈ _ (by decide), u₇.other _ (by decide), g₆ _ (by decide), xbx]
    · rw [e₈, u₇.other _ (by decide), g₆ _ (by decide), xd]
    · intro r a b c d e
      rw [g₈ r e, u₇.other r c, g₆ r a, xo r a b c d e]
    · rw [m₈, u₇.mem, m₆, xm]
    · rw [rd₈, u₇.rd, rd₆, xrd]
    · rw [wr₈, u₇.wr, wr₆, xwr]
    · rw [sy₈, u₇.syms, sy₆, xsy]
  refine WP.seq (WP.ite (decide (witLen - used = 0)) H.zf (fun hz => ld_ok hs₅ (by omega_using [szs]) fun s₆ u₆ =>
    WP.block_nil (tail s₆ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)) (fun hz => WP.block_nil (tail t edi₅ ?_ H.ebx H.other H.mem H.rd
      H.wr H.syms)))
  · rw [u₆.other _ (by decide), edi₅]
  · have h0 : witLen - used = 0 := by simpa using hz
    rw [u₆.gpr, H.mem, hW]; simp only [randPtr, h0, ↓reduceIte]
  · rw [u₆.other _ (by decide), H.ebx]
  · intro r a b c d e; rw [u₆.other r d, H.other r a b c d e]
  · rw [u₆.mem, H.mem]
  · rw [u₆.rd, H.rd]
  · rw [u₆.wr, H.wr]
  · rw [u₆.syms, H.syms]
  · have h0 : ¬ witLen - used = 0 := by simpa using hz
    rw [H.edx]; simp only [randPtr, h0, ↓reduceIte]

theorem testArgs_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) (hsz : sPP ≤ size)
    {W : BitVec 32} {witLen used : Nat} (hW : s.mem.readW (off base fWit) 32 = W)
    (hWL : s.mem.readW (off base fWitLen) 32 = BitVec.ofNat 32 witLen)
    (hU : s.mem.readW (off base fUsed) 32 = BitVec.ofNat 32 used) (hu : used ≤ witLen)
    (hwl : witLen < 2 ^ 32) {rest : Prog isa} {Q : State → Prop}
    (k : ∀ t, TestArgs base W witLen used s t → WP isa rest t Q) :
    WP isa (.seq (.block [.mov .ecx (.mem (sc fUsed)), .mov .edx (.mem (sc fWit)), .alu .add .edx (.reg .ecx),
        .mov .ebx (.mem (sc fWitLen)), .alu .sub .ebx (.reg .ecx)])
      (.seq (.ite .e (.block [.mov .edx (.mem (sc fWit))]) (.block []))
        (.seq (.block (scr .eax sPP ++ ([.mov .ecx (.imm (BitVec.ofNat 32 ppWords))] : List Instr) ++ scr .ebp fUsedOut)) rest))) s
      Q :=
  WP.seq (WP.mono (testHead_ok hs hsz hW hWL hU hu hwl) fun _ H =>
    WP.assoc (WP.seq (WP.mono (testMid_ok hs hsz hW H) k)))

end VG.Proof.Dsa.X86.Generation
end

end

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation

/-- The registers a test's call pushes, last argument first. -/
abbrev testRegs : List Reg := [.ebp, .ebx, .edx, .ecx, .eax]

/-- The test's contract, as `Generic/MillerRabin/X86/DsaProbablePrime.lean`
registers it. -/
abbrev ppContract (bits : Nat) : Contract isa :=
  Proof.Dsa.ProbablePrime.contract (VG.Impl.Dsa.X86.ProbablePrime.layout bits)
    (abi.withConsts VG.Impl.RsaKeyGen.TrialTable32.consts) 152

/-- The regions the test is given: the witnesses left and the table, and the
working space, `used` and the arguments. -/
def randAddr (E : Env) (used : Nat) : Addr :=
  if E.witLen - used = 0 then E.wit else E.wit + BitVec.ofNat 64 used

def testRd (E : Env) (used : Nat) : List Region :=
  [⟨randAddr E used, E.witLen - used⟩, E.tableRegion]

def testWr (E : Env) (s : State) : List Region :=
  [⟨off E.base sPP, 8 * ppWords⟩, ⟨off E.base fUsedOut, 8⟩, ⟨(s.gpr .esp - 20#32).setWidth 64, 20⟩]

/-- The state the test starts in. -/
abbrev testEntry (E : Env) (used : Nat) (s : State) : State :=
  (pushed testRegs s).callEntry.withRegions (testRd E used) (testWr E s)

theorem packed_len : VG.Impl.RsaKeyGen.TrialTable32.packed.length = 1024 := by
  simp [VG.Impl.RsaKeyGen.TrialTable32.packed]

/-- A part of a region, by its start and length. -/
theorem sub_of_contains {R : Region} {a : Addr} {n : Nat} (h : R.Contains a n) : Region.Sub ⟨a, n⟩ R :=
  fun _ hx => h.byte (by simp only [Region.Contains] at hx; omega_using [hx])

theorem randPtr_toNat {E : Env} (v : E.Valid) {used : Nat} (hu : used ≤ E.witLen) :
    (randPtr (E.wit.setWidth 32) E.witLen used).toNat = (randAddr E used).toNat := by
  have witLt := v.witPtr
  have wf := v.witFit
  obtain w32 : (E.wit.setWidth 32).toNat = E.wit.toNat := by
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt witLt]
  by_cases h0 : E.witLen - used = 0
  · simp only [randPtr, randAddr, h0, ↓reduceIte, w32]
  · have e1 : (E.wit.setWidth 32 + BitVec.ofNat 32 used).toNat = E.wit.toNat + used := by
      rw [BitVec.toNat_add, w32, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := used) (by omega_using [wf, h0]),
        Nat.mod_eq_of_lt (by omega_using [wf, h0])]
    obtain e2 : (E.wit + BitVec.ofNat 64 used).toNat = E.wit.toNat + used := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := used) (by omega_using [e1]),
        Nat.mod_eq_of_lt (by omega_using [hu, wf])]
    simp only [randPtr, randAddr, h0, ↓reduceIte, e1, e2]

theorem randPtr_wide {E : Env} (v : E.Valid) {used : Nat} (hu : used ≤ E.witLen) :
    (randPtr (E.wit.setWidth 32) E.witLen used).setWidth 64 = randAddr E used :=
  BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_setWidth, randPtr_toNat v hu, Nat.mod_eq_of_lt (by
    have := (randPtr (E.wit.setWidth 32) E.witLen used).isLt; rw [randPtr_toNat v hu] at this; omega_using [])])

theorem randAddr_fit {E : Env} (v : E.Valid) {used : Nat} (hu : used ≤ E.witLen) :
    (randAddr E used).toNat + (E.witLen - used) ≤ 2 ^ 32 := by
  have wf := v.witFit
  by_cases h0 : E.witLen - used = 0
  · simp only [randAddr, h0, ↓reduceIte]; omega_using [wf]
  · have e2 : (E.wit + BitVec.ofNat 64 used).toNat = E.wit.toNat + used := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := used) (by omega_using [hu, wf]),
        Nat.mod_eq_of_lt (by omega_using [hu, wf])]
    simp only [randAddr, h0, ↓reduceIte, e2]; omega_using [hu, wf]

theorem randAddr_sub {E : Env} {used : Nat} (hu : used ≤ E.witLen) :
    Region.Sub ⟨randAddr E used, E.witLen - used⟩ E.witRegion := by
  by_cases h0 : E.witLen - used = 0
  · intro x hx; simp only [Region.Contains, h0] at hx; omega
  · simp only [randAddr, h0, ↓reduceIte]
    exact Offset.sub_base E.wit (by omega_using [hu])

/-- The witnesses left, in memory that holds the tape. -/
theorem rand_bytes {E : Env} {used : Nat} {m : Mem}
    (hm : Spec.Rsa.bytesAt m E.wit E.witLen = E.witT) :
    Spec.Rsa.bytesAt m (randAddr E used) (E.witLen - used) = E.witT.drop used := by
  rw [← hm]
  by_cases h0 : E.witLen - used = 0
  · simp only [randAddr, h0, ↓reduceIte, Spec.Rsa.bytesAt, List.range_zero, List.map_nil]
    exact (List.drop_eq_nil_of_le (by simp; omega_using [h0])).symm
  · simp only [randAddr, h0, ↓reduceIte, Spec.Rsa.bytesAt]
    apply List.ext_getElem (by simp)
    intro i h₁ h₂
    simp only [List.getElem_map, List.getElem_range, List.getElem_drop]
    rw [VG.Offset.add_add]

/-- The test's arguments, from the registers pushed. -/
theorem testEntry_arg {E : Env} {used : Nat} {s : State} (fit : 24 ≤ (s.gpr .esp).toNat) :
    arg (testEntry E used s) 0 = s.gpr .eax ∧ arg (testEntry E used s) 1 = s.gpr .ecx ∧
      arg (testEntry E used s) 2 = s.gpr .edx ∧ arg (testEntry E used s) 3 = s.gpr .ebx ∧
      arg (testEntry E used s) 4 = s.gpr .ebp := by
  obtain fit' : 4 * testRegs.length + 4 ≤ (s.gpr .esp).toNat := by simpa using fit
  obtain hrs : Reg.esp ∉ testRegs := by decide
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    (rw [testEntry, arg_withRegions, callEntry_arg fit' hrs (by decide)]; rfl)

theorem testEntry_mem {E : Env} {used : Nat} {s : State} (fit : 24 ≤ (s.gpr .esp).toNat) :
    Frame [below (s.gpr .esp) 24] s.mem (testEntry E used s).mem :=
  callEntry_frame (rs := testRegs) (by simpa using fit) (by decide)

/-- A test's candidate keeps its value through writes to the stack. -/
theorem cand_frame {E : Env} (v : E.Valid) {bits : Nat}
    (lay : (VG.Impl.Dsa.X86.ProbablePrime.layout bits).size ≤ 8 * ppWords) {k : Nat} (hk : k ≤ 200)
    {m m' : Mem} (F : Frame [below E.sp k] m m') :
    Proof.Dsa.ProbablePrime.candidateAt (VG.Impl.Dsa.X86.ProbablePrime.layout bits) m' (off E.base sPP) =
      Proof.Dsa.ProbablePrime.candidateAt (VG.Impl.Dsa.X86.ProbablePrime.layout bits) m (off E.base sPP) := by
  have sz := v.size_ge
  have low := v.low
  obtain lay' : (VG.Impl.Dsa.X86.ProbablePrime.layout bits).candidate + bits / 8 ≤ ppWords * 8 := by
    simp only [VG.Impl.Dsa.X86.ProbablePrime.layout] at lay ⊢; omega_using [lay]
  unfold Proof.Dsa.ProbablePrime.candidateAt
  refine congrArg Spec.Dsa.decodeBE ?_
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  simp only [List.mem_range] at hi
  obtain subWS : Region.Sub ⟨off E.base sPP, ppWords * 8⟩ E.scratchRegion :=
    Offset.sub_base _ (by simp only [sPP, ppWords]; omega_using [sz])
  obtain sub : Region.Sub ⟨off E.base sPP + BitVec.ofNat 64 (VG.Impl.Dsa.X86.ProbablePrime.layout bits).candidate,
      bits / 8⟩ ⟨off E.base sPP, ppWords * 8⟩ := Offset.sub_base _ (by simpa using lay')
  have lb : (VG.Impl.Dsa.X86.ProbablePrime.layout bits).bits = bits := rfl
  rw [lb] at hi
  refine Frame.bytes F (R := ⟨_, bits / 8⟩) ?_ (by
      show bits / 8 ≤ 2 ^ 64; simp only [VG.Impl.Dsa.X86.ProbablePrime.layout, ppWords] at lay; omega_using [lay])
    (by simpa using hi)
  intro r hr; simp only [List.mem_singleton] at hr; subst hr
  exact ((v.scratchStack.sub_left subWS).sub_left sub).sub_right (below_sub hk (by omega_using [low]))

theorem test_pre {bits : Nat} {E : Env} (v : E.Valid) {s₀ s : State} (B : Base E s₀) {used : Nat}
    (A : TestArgs E.base (E.wit.setWidth 32) E.witLen used s₀ s) (hu : used ≤ E.witLen)
    (lay : (VG.Impl.Dsa.X86.ProbablePrime.layout bits).size ≤ 8 * ppWords)
    (odd : Proof.Dsa.ProbablePrime.candidateAt (VG.Impl.Dsa.X86.ProbablePrime.layout bits) s.mem
      (off E.base sPP) % 2 = 1)
    (len : Spec.Dsa.bitLength (Proof.Dsa.ProbablePrime.candidateAt (VG.Impl.Dsa.X86.ProbablePrime.layout bits)
      s.mem (off E.base sPP)) = bits) :
    (ppContract bits).pre (testEntry E used s) := by
  have sp := B.sp
  obtain spU : s.gpr .esp = E.sp := by rw [A.other _ (by decide) (by decide) (by decide) (by decide) (by decide), sp]
  have low := v.low
  have spLt := E.sp.isLt
  have nw := v.scratchFit
  have room := v.room
  have wf := v.witFit
  have tf := v.tableFit
  obtain fit : 4 * testRegs.length + 4 ≤ (s.gpr .esp).toNat := by rw [spU]; simp only [List.length_cons, List.length_nil]; omega_arith
  obtain hrs : Reg.esp ∉ testRegs := by decide
  obtain nat24 : (s.gpr .esp - 24#32).toNat = E.sp.toNat - 24 := by rw [spU]; exact sub_toNat (by omega_arith)
  obtain nat20 : ((s.gpr .esp - 20#32).setWidth 64).toNat = E.sp.toNat - 20 := by
    rw [BitVec.toNat_setWidth, spU, sub_toNat (by omega_arith)]; exact Nat.mod_eq_of_lt (by omega_arith)
  obtain uesp : (testEntry E used s).gpr .esp = s.gpr .esp - 24#32 := by
    change (pushed testRegs s).callEntry.gpr .esp = _
    exact callEntry_esp' testRegs s
  obtain uarg0 : argAddr (testEntry E used s) 0 = (s.gpr .esp - 20#32).setWidth 64 := by
    rw [testEntry, argAddr_withRegions]; exact callEntry_argAddr0 testRegs s
  obtain ua : ∀ i (hi : i < 5), arg (testEntry E used s) i = arg (pushed testRegs s).callEntry i := fun i _ => by
    rw [testEntry, arg_withRegions]
  obtain a0 : arg (testEntry E used s) 0 = s₀.gpr .edi + BitVec.ofNat 32 sPP := by
    rw [ua 0 (by decide), callEntry_arg fit hrs (by decide)]; exact A.eax
  obtain a1 : arg (testEntry E used s) 1 = BitVec.ofNat 32 ppWords := by
    rw [ua 1 (by decide), callEntry_arg fit hrs (by decide)]; exact A.ecx
  obtain a2 : arg (testEntry E used s) 2 = randPtr (E.wit.setWidth 32) E.witLen used := by
    rw [ua 2 (by decide), callEntry_arg fit hrs (by decide)]; exact A.edx
  obtain a3 : arg (testEntry E used s) 3 = BitVec.ofNat 32 (E.witLen - used) := by
    rw [ua 3 (by decide), callEntry_arg fit hrs (by decide)]; exact A.ebx
  obtain a4 : arg (testEntry E used s) 4 = s₀.gpr .edi + BitVec.ofNat 32 fUsedOut := by
    rw [ua 4 (by decide), callEntry_arg fit hrs (by decide)]; exact A.ebp
  have urd : (testEntry E used s).rd = testRd E used := rfl
  have uwr : (testEntry E used s).wr = testWr E s := rfl
  have usy : (testEntry E used s).syms = s.syms := rfl
  obtain umem : Frame [below (s.gpr .esp) (4 * testRegs.length + 4)] s.mem (testEntry E used s).mem :=
    callEntry_frame fit hrs
  generalize eu : testEntry E used s = u at *
  sig_pre [ppContract, Proof.Dsa.ProbablePrime.contract, Proof.Dsa.ProbablePrime.sig, abi,
    argSlots, argVal, argBytes, Abi.withConsts, VG.Impl.RsaKeyGen.TrialTable32.consts, stackBelow]
  have hs := B.scr
  have sz := v.size_ge
  have witLt := v.witPtr
  have lenLt := v.witLen32
  obtain wsW := Scr.wide hs (d := sPP) (by simp only [sPP]; omega_arith)
  obtain uoW := Scr.wide hs (d := fUsedOut) (by simp only [fUsedOut, hdr]; omega_arith)
  obtain wsN := Scr.toNat_add hs (d := sPP) (by simp only [sPP]; omega_arith)
  obtain uoN := Scr.toNat_add hs (d := fUsedOut) (by simp only [fUsedOut, hdr]; omega_arith)
  obtain randW := randPtr_wide v (used := used) hu
  obtain randN := randPtr_toNat v (used := used) hu
  obtain randFit := randAddr_fit v (used := used) hu
  obtain randSub := randAddr_sub (E := E) (used := used) hu
  obtain lenN : (BitVec.ofNat 32 (E.witLen - used)).toNat = E.witLen - used := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
  obtain ppN : (BitVec.ofNat 32 ppWords).toNat = ppWords := by decide
  obtain callee : (s.gpr .esp - 24#32).setWidth 64 - 152#64 = (s.gpr .esp - 176#32).setWidth 64 := by
    rw [← Taint.sub_setWidth (by rw [nat24]; omega_arith : 152 ≤ (s.gpr .esp - 24#32).toNat), BitVec.sub_sub]; rfl
  have sy₀ : s.syms = s₀.syms := A.syms
  have m₀ : s.mem = s₀.mem := A.mem
  simp only [a0, a1, a2, a3, a4, uesp, uarg0, urd, uwr, usy, testRd, testWr, wsW, uoW, randW, randN, lenN,
    ppN, wsN, uoN, callee, Abi.constRegions_cons, Abi.constRegions_nil, packed_len, List.length_cons,
    List.length_nil, List.drop, List.take, Nat.reduceSub, Nat.reduceAdd, Nat.reduceMul]
  obtain symT : (s.syms VG.Impl.RsaKeyGen.TrialTable32.symbol).setWidth 64 = E.table := by rw [sy₀]; exact B.syms
  obtain subWS : Region.Sub ⟨off E.base sPP, ppWords * 8⟩ E.scratchRegion :=
    Offset.sub_base _ (by simp only [sPP, ppWords]; omega_arith)
  obtain subUO : Region.Sub ⟨off E.base fUsedOut, 8⟩ E.scratchRegion :=
    Offset.sub_base _ (by simp only [fUsedOut, hdr]; omega_arith)
  obtain subArgs : Region.Sub ⟨(s.gpr .esp - 20#32).setWidth 64, 20⟩ E.stackRegion := by
    rw [spU]; exact below_sub (by decide) (by omega_arith)
  obtain subRet : Region.Sub ⟨(s.gpr .esp - 24#32).setWidth 64, 4⟩ E.stackRegion :=
    sub_of_contains (by rw [spU]; exact below_top (k := 24) (by decide) (by omega_arith) (by decide))
  obtain subCal : Region.Sub ⟨(s.gpr .esp - 176#32).setWidth 64, 152⟩ E.stackRegion :=
    sub_of_contains (by rw [spU]; exact below_top (k := 176) (by decide) (by omega_arith) (by decide))
  obtain subPush : Region.Sub (below (s.gpr .esp) (4 * testRegs.length + 4)) E.stackRegion := by
    rw [spU]; exact below_sub (by decide) (by omega_arith)
  have ss := v.scratchStack
  obtain wf := v.tapesFar E.witRegion (by simp)
  obtain ws := wf.1; have wk := wf.2.2
  obtain ts := v.tableFar.1; have tk := v.tableFar.2.2
  obtain nat136 : ((s.gpr .esp - 176#32).setWidth 64).toNat = E.sp.toNat - 176 := by
    rw [BitVec.toNat_setWidth, spU, sub_toNat (by omega_arith)]; exact Nat.mod_eq_of_lt (by omega_arith)
  obtain nat24' : ((s.gpr .esp - 24#32).setWidth 64).toNat = E.sp.toNat - 24 := by
    rw [BitVec.toNat_setWidth, nat24]; exact Nat.mod_eq_of_lt (by omega_arith)
  obtain retArgs : Region.Disjoint ⟨(s.gpr .esp - 24#32).setWidth 64, 4⟩ ⟨(s.gpr .esp - 20#32).setWidth 64, 20⟩ :=
    Offset.disjoint_of_le (by simp only [nat24', nat20]; omega_arith) (by simp only [nat20]; omega_arith)
  obtain calArgs : Region.Disjoint ⟨(s.gpr .esp - 176#32).setWidth 64, 152⟩ ⟨(s.gpr .esp - 20#32).setWidth 64, 20⟩ :=
    Offset.disjoint_of_le (by simp only [nat136, nat20]; omega_arith) (by simp only [nat20]; omega_arith)
  obtain wsUO : Region.Disjoint ⟨off E.base sPP, ppWords * 8⟩ ⟨off E.base fUsedOut, 8⟩ :=
    Offset.disjoint E.base (by simp only [sPP, ppWords, fUsedOut, hdr]; omega_arith) (by simp only [sPP, ppWords]; omega_arith)
      (by simp only [fUsedOut, hdr]; omega_arith)
  obtain candEq : ∀ m : Mem, Frame [below (s.gpr .esp) (4 * testRegs.length + 4)] s.mem m →
      Proof.Dsa.ProbablePrime.candidateAt (VG.Impl.Dsa.X86.ProbablePrime.layout bits) m (off E.base sPP) =
        Proof.Dsa.ProbablePrime.candidateAt (VG.Impl.Dsa.X86.ProbablePrime.layout bits) s.mem (off E.base sPP) :=
    fun m F => cand_frame v lay (k := 24) (by decide) (by simpa [spU] using F)
  refine ⟨by omega_arith, by omega_arith, by rw [symT]; rfl, ?_, ?_, fun t ht => by
    simp only [List.mem_singleton] at ht; subst ht; dsimp only; rw [symT]; exact v.tableAligned, trivial, by rw [Nat.mul_comm 8 ppWords],
    (ws.symm.sub_left subWS).sub_right randSub, wsUO, (ss.sub_left subWS).sub_right subArgs,
    (ws.sub_left randSub).sub_right subUO, (wk.sub_left randSub).sub_right subArgs,
    (ss.sub_left subUO).sub_right subArgs,
    (ss.symm.sub_left subRet).sub_right subWS, (wk.symm.sub_left subRet).sub_right randSub,
    (ss.symm.sub_left subRet).sub_right subUO, retArgs,
    (ss.symm.sub_left subCal).sub_right subWS, (wk.symm.sub_left subCal).sub_right randSub,
    (ss.symm.sub_left subCal).sub_right subUO, calArgs,
    by simp only [sPP, ppWords]; omega_arith, randFit, by simp only [fUsedOut, hdr]; omega_arith,
    by simpa [VG.Impl.Dsa.X86.ProbablePrime.layout] using lay, by rw [candEq _ umem]; exact odd,
    by rw [candEq _ umem]; exact len⟩
  · intro c hc i hi
    obtain h := B.held c hc i hi
    simp only [List.mem_singleton] at hc
    subst hc
    simp only at h ⊢
    rw [symT]
    rw [← sy₀, symT] at h
    rw [← h, ← m₀]
    obtain len : i < 1024 := by simpa [packed_len] using hi
    refine Frame.readW umem (r := E.tableRegion) (Offset.contains_base E.table (by omega_arith) (by omega_arith)) ?_ (by decide)
    intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact tk.sub_right subPush
  · intro t ht
    simp only [List.mem_singleton] at ht
    subst ht
    rw [symT]
    refine ⟨by omega_arith, ?_, tk.sub_right subRet, tk.sub_right subCal⟩
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ts.sub_right (by rw [Nat.mul_comm]; exact subWS)
    · exact ts.sub_right subUO
    · exact tk.sub_right subArgs

end VG.Proof.Dsa.X86.Generation

end

end

/-! # What parameter generation needs of the functions it calls

For one of the three sizes: the hash function's code and initial value,
proven to be the seed hash of FIPS 186-4 A.1.1.2 for the subgroup's size,
and the verified probable-prime tests and domain check it calls. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Dsa.X86.Generation

structure GeoOk (g : Geo) where
  lengths : (g.pLen = 128 ∧ g.qLen = 20) ∨ (g.pLen = 256 ∧ g.qLen = 32) ∨ (g.pLen = 384 ∧ g.qLen = 32)
  hash : HashOk g.H g.iv
  N : g.H.N = g.qLen
  seedHash : ∀ m, hash.ok.hH.SH.H.hash m = Spec.Dsa.seedHash (8 * g.qLen) m
  e : g.e = (8 * g.pLen - 8 * g.qLen) / 32 + 1
  qv : Verified target g.qCode (ppContract (8 * g.qLen))
  qNoSp : NoSp g.qCode
  qStack : stackUse g.qCode ≤ 152
  pv : Verified target g.pCode (ppContract (8 * g.pLen))
  pNoSp : NoSp g.pCode
  pStack : stackUse g.pCode ≤ 152
  cv : Verified target g.checkCode (Proof.Dsa.checkParametersContract abi 108)
  cNoSp : NoSp g.checkCode
  cStack : stackUse g.checkCode ≤ 108
  /-- The hash's blocks: their traces depend only on `esp` and `edi`, and
  they keep `esp`. -/
  prepCt : RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi]))
    (.block (scr .ebx sState ++ ivStore g.iv ++
      Impl.Pbkdf2.Md.X86.storeW .ebx (g.H.N + g.qLen) (padBytes g.qLen) ((64 - g.qLen) / 4) ++
      [.mov .eax (.reg .ebx), .alu .add .eax (.imm (BitVec.ofNat 32 g.H.N))] ++ scr .ebp sHScr)) fun _ _ => True
  outCt : ∀ dst, RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi]))
    (.block (scr .ebx sState ++ scr .eax dst ++ g.H.out)) fun _ _ => True
  outNoSp : ∀ i ∈ g.H.out, Taint.clobbers i .esp = false

theorem GeoOk.bounds {g : Geo} (G : GeoOk g) :
    20 ≤ g.qLen ∧ g.qLen ≤ 32 ∧ 128 ≤ g.pLen ∧ g.pLen ≤ 384 ∧ (g.count + 1) * g.qLen ≤ g.pLen + 12 ∧
      g.pLen ≤ (g.count + 1) * g.qLen := by
  unfold Geo.count
  rcases G.lengths with ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ <;> rw [h, h'] <;> decide

end VG.Proof.Dsa.X86.Generation
