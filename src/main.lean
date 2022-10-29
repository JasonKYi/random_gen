import control.random

open io

/-! # Uniform generation -/

def random_num (n : ℕ) : io ℕ := 
io.rand 1 n

-- Given some seed, we generate a random number in `{1, ..., n}`.
#eval random_num 37 >>= print

def random_num_list' (n : ℕ) (m : ℕ) : list (io ℕ) :=
list.map (λ _, random_num n) (list.range m) 

def print_list_io {α : Type*} [has_to_string α] : list (io α) → io (list α)
| [] := return []
| (x :: xs) := do
  x' ← x,
  xs' ← print_list_io xs,
  return (x' :: xs')

-- Generate a list of random numbers uniformly in `{1, ..., n}` of size `m`.
def random_num_list (n : ℕ) (m : ℕ) : io (list ℕ) :=
print_list_io $ random_num_list' n m

#eval random_num_list 37 100 >>= print

/-! # Generation given some distribution -/

def normalize_distrib' : list ℕ → list ℕ 
| [] := []
| (x :: xs) := (list.sum (x :: xs)) :: normalize_distrib' xs

def normalize_distrib : list ℕ → list ℕ :=
list.reverse ∘ normalize_distrib' ∘ list.reverse

def list.mono (l : list ℕ) : Prop :=
∀ (n : ℕ) (hn : n.succ < l.length), l.nth_le n (n.lt_succ_self.trans hn) ≤ l.nth_le n.succ hn

lemma normalize_distrib_mono {l : list ℕ} : list.mono (normalize_distrib l) :=
sorry

@[derive [decidable_pred]]
def list.placed (l : list ℕ) (n : ℕ) (i : ℕ) : Prop :=
if hi : i < l.length then n ≤ l.nth_le i hi else false

lemma lt_length_of_placed {l : list ℕ} {n : ℕ} {i : ℕ} (h : l.placed n i) : 
  i < l.length :=
begin
  rw [list.placed] at h,
  split_ifs at h with hi hi,
  exacts [hi, false.elim h],
end

lemma exists_placed_iff {l : list ℕ} {n : ℕ} : 
  (∃ i, l.placed n i) ↔ (∃ i, i < l.length ∧ l.placed n i) :=
⟨λ ⟨i, h⟩, ⟨i, lt_length_of_placed h, h⟩, λ ⟨i, _, h⟩, ⟨i, h⟩⟩

instance {l : list ℕ} {n : ℕ} : decidable (∃ i, l.placed n i) :=
decidable_of_iff' _ exists_placed_iff

def list.place (l : list ℕ) (hmono : l.mono) (n : ℕ) : ℕ :=
if hi : ∃ i, l.placed n i then @nat.find (l.placed n) infer_instance hi else l.length

def list.distribute (distrib : list ℕ) (hmono : distrib.mono) : 
  list ℕ → list ℕ
| [] := []
| (x :: xs) := distrib.place hmono x :: list.distribute xs

def random_num_list_distrib (m : ℕ) (distrib : list ℕ) : io (list ℕ) := do 
  rnd ← random_num_list (list.sum distrib) m,
  return ((normalize_distrib distrib).distribute normalize_distrib_mono rnd)
  
#eval random_num_list_distrib 100 [0, 0, 8, 9, 8, 9] >>= print



