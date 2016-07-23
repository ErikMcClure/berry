// Copyright ©2016 Black Sphere Studios
// For conditions of distribution and use, see copyright notice in LICENSE.txt

// Define fundamental traits and implement them on base types
trait integral {};
trait sint_t {};
trait uint_t {};
trait fp_t {};
trait unsafe_pointer_t {};

impl i8:sint_t;
impl i8:integral;
impl i16:sint_t;
impl i16:integral;
impl i32:sint_t;
impl i32:integral;
impl i64:sint_t;
impl i64:integral;
impl int:sint_t;
impl int:integral;
impl u8:uint_t;
impl u8:integral;
impl u16:uint_t;
impl u16:integral;
impl u32:uint_t;
impl u32:integral;
impl u64:uint_t;
impl u64:integral;
impl uint:uint_t;
impl uint:integral;

impl f16:fp_t;
impl f32:fp_t;
impl f64:fp_t;

// Trunc and extend don't allow equal bit sizes, so we must take care of those up here.
// Which of these conversions are implicit is carefully chosen.
implicit i8 op(u8 i) { i8 v; llvm { %v = bitcast u8 %i to i8 } return v; }
implicit i16 op(u16 i) { i16 v; llvm { %v = bitcast u16 %i to i16 } return v; }
implicit i32 op(u32 i) { i32 v; llvm { %v = bitcast u32 %i to i32 } return v; }
implicit i64 op(u64 i) { i64 v; llvm { %v = bitcast u64 %i to i64 } return v; }
u8 op(i8 i) { u8 v; llvm { %v = bitcast i8 %i to u8 } return v; }
u16 op(i16 i) { u16 v; llvm { %v = bitcast i16 %i to u16 } return v; }
u32 op(i32 i) { u32 v; llvm { %v = bitcast i32 %i to u32 } return v; }
u64 op(i64 i) { u64 v; llvm { %v = bitcast i64 %i to u64 } return v; }

// Integer conversion gets tricky and has some subtle edge cases, so we don't use templates here.
implicit u16 op(u8 i) { u16 v; llvm { %v = zext u8 %i to u16 } return v; }
implicit u32 op(u8 i) { u32 v; llvm { %v = zext u8 %i to u32 } return v; }
implicit u64 op(u8 i) { u64 v; llvm { %v = zext u8 %i to u64 } return v; }
implicit i16 op(u8 i) { i16 v; llvm { %v = zext u8 %i to i16 } return v; }
implicit i32 op(u8 i) { i32 v; llvm { %v = zext u8 %i to i32 } return v; }
implicit i64 op(u8 i) { i64 v; llvm { %v = zext u8 %i to i64 } return v; }
implicit u32 op(u16 i) { u32 v; llvm { %v = zext u16 %i to u32 } return v; }
implicit u64 op(u16 i) { u64 v; llvm { %v = zext u16 %i to u64 } return v; }
implicit i32 op(u16 i) { i32 v; llvm { %v = zext u16 %i to i32 } return v; }
implicit i64 op(u16 i) { i64 v; llvm { %v = zext u16 %i to i64 } return v; }
implicit u64 op(u32 i) { u64 v; llvm { %v = zext u32 %i to u64 } return v; }
implicit i64 op(u32 i) { i64 v; llvm { %v = zext u32 %i to i64 } return v; }

implicit i16 op(i8 i) { i16 v; llvm { %v = sext i8 %i to i16 } return v; }
implicit i32 op(i8 i) { i32 v; llvm { %v = sext i8 %i to i32 } return v; }
implicit i64 op(i8 i) { i64 v; llvm { %v = sext i8 %i to i64 } return v; }
implicit i32 op(i16 i) { i32 v; llvm { %v = sext i16 %i to i32 } return v; }
implicit i64 op(i16 i) { i64 v; llvm { %v = sext i16 %i to i64 } return v; }
implicit i64 op(i32 i) { i64 v; llvm { %v = sext i32 %i to i64 } return v; }

u8 op(u16 i) { u8 v; llvm { %v = trunc u16 %i to u8 } return v; }
u8 op(u32 i) { u8 v; llvm { %v = trunc u32 %i to u8 } return v; }
u8 op(u64 i) { u8 v; llvm { %v = trunc u64 %i to u8 } return v; }
u8 op(i16 i) { u8 v; llvm { %v = trunc i16 %i to u8 } return v; }
u8 op(i32 i) { u8 v; llvm { %v = trunc i32 %i to u8 } return v; }
u8 op(i64 i) { u8 v; llvm { %v = trunc i64 %i to u8 } return v; }
i8 op(u16 i) { i8 v; llvm { %v = trunc u16 %i to i8 } return v; }
i8 op(u32 i) { i8 v; llvm { %v = trunc u32 %i to i8 } return v; }
i8 op(u64 i) { i8 v; llvm { %v = trunc u64 %i to i8 } return v; }
i8 op(i16 i) { i8 v; llvm { %v = trunc i16 %i to i8 } return v; }
i8 op(i32 i) { i8 v; llvm { %v = trunc i32 %i to i8 } return v; }
i8 op(i64 i) { i8 v; llvm { %v = trunc i64 %i to i8 } return v; }
u16 op(u32 i) { u16 v; llvm { %v = trunc u32 %i to u16 } return v; }
u16 op(u64 i) { u16 v; llvm { %v = trunc u64 %i to u16 } return v; }
u16 op(i32 i) { u16 v; llvm { %v = trunc i32 %i to u16 } return v; }
u16 op(i64 i) { u16 v; llvm { %v = trunc i64 %i to u16 } return v; }
i16 op(u32 i) { i16 v; llvm { %v = trunc u32 %i to i16 } return v; }
i16 op(u64 i) { i16 v; llvm { %v = trunc u64 %i to i16 } return v; }
i16 op(i32 i) { i16 v; llvm { %v = trunc i32 %i to i16 } return v; }
i16 op(i64 i) { i16 v; llvm { %v = trunc i64 %i to i16 } return v; }
u32 op(u64 i) { u32 v; llvm { %v = trunc u64 %i to u32 } return v; }
u32 op(i64 i) { u32 v; llvm { %v = trunc i64 %i to u32 } return v; }
i32 op(u64 i) { i32 v; llvm { %v = trunc u64 %i to i32 } return v; }
i32 op(i64 i) { i32 v; llvm { %v = trunc i64 %i to i32 } return v; }

implicit f32 op(f16 f) { f32 v; llvm { %v = fpext f16 %f to f32 } return v; }
implicit f64 op(f16 f) { f64 v; llvm { %v = fpext f16 %f to f64 } return v; }
implicit f64 op(f32 f) { f64 v; llvm { %v = fpext f32 %f to f64 } return v; }

f16 op(f32 f) { f16 v; llvm { %v = fptrunc f32 %f to f16 } return v; }
f16 op(f64 f) { f16 v; llvm { %v = fptrunc f64 %f to f16 } return v; }
f32 op(f64 f) { f32 v; llvm { %v = fptrunc f64 %f to f32 } return v; }

// Integer to floating point conversions
template[T:fp_t, U:uint_t]
U op(T f) { U v; llvm { %v = fptoui T %f to U } return v; }

template[T:fp_t, U:sint_t]
U op(T f) { U v; llvm { %v = fptosi T %f to U } return v; }

template[T:uint_t, U:fp_t]
U op(T i) { U v; llvm { %v = uitofp T %i to U } return v; }

template[T:sint_t, U:fp_t]
U op(T i) { U v; llvm { %v = sitofp T %i to U } return v; }

// Unsafe pointer to integer conversions
template[T:unsafe_pointer_t, U = uint]
U op(T p) { U v; llvm { %v = ptrtoint T %p to U } return v; }

template[T = uint, U:unsafe_pointer_t]
U op(T i) { U v; llvm { %v = inttoptr T %i to U } return v; }

// Arithmetic and comparison operations
template[T:integral]
T op+(T l, T r) { T v; llvm { %v = add T %l, %r } return v; }
template[T:integral]
T op-(T l, T r) { T v; llvm { %v = sub T %l, %r } return v; }
template[T:integral]
T op*(T l, T r) { T v; llvm { %v = mul T %l, %r } return v; }
template[T:integral]
T op<<(T l, T r) { T v; llvm { %v = shl T %l, %r } return v; }
template[T:integral]
T op>>(T l, T r) { T v; llvm { %v = lshr T %l, %r } return v; }
template[T:integral]
T op>>>(T l, T r) { T v; llvm { %v = ashr T %l, %r } return v; }
template[T:integral]
T op&(T l, T r) { T v; llvm { %v = and T %l, %r } return v; }
template[T:integral]
T op|(T l, T r) { T v; llvm { %v = or T %l, %r } return v; }
template[T:integral]
T op^(T l, T r) { T v; llvm { %v = xor T %l, %r } return v; }
template[T:integral]
bool op==(T l, T r) { bool v; llvm { %v = icmp eq T %l, %r } return v; } // Note: A bool is an i1 type in LLVM
template[T:integral]
bool op!=(T l, T r) { bool v; llvm { %v = icmp ne T %l, %r } return v; }

template[T:uint_t]
T op/(T l, T r) { T v; llvm { %v = udiv T %l, %r } return v; }
template[T:uint_t]
T op%%(T l, T r) { T v; llvm { %v = urem T %l, %r } return v; }
template[T:uint_t]
bool op>(T l, T r) { bool v; llvm { %v = icmp ugt T %l, %r } return v; }
template[T:uint_t]
bool op>=(T l, T r) { bool v; llvm { %v = icmp uge T %l, %r } return v; }
template[T:uint_t]
bool op<(T l, T r) { bool v; llvm { %v = icmp ult T %l, %r } return v; }
template[T:uint_t]
bool op<=(T l, T r) { bool v; llvm { %v = icmp ule T %l, %r } return v; }

template[T:sint_t]
T op/(T l, T r) { T v; llvm { %v = sdiv T %l, %r } return v; }
template[T:sint_t]
T op%%(T l, T r) { T v; llvm { %v = srem T %l, %r } return v; }
template[T:sint_t]
bool op>(T l, T r) { bool v; llvm { %v = icmp sgt T %l, %r } return v; }
template[T:sint_t]
bool op>=(T l, T r) { bool v; llvm { %v = icmp sge T %l, %r } return v; }
template[T:sint_t]
bool op<(T l, T r) { bool v; llvm { %v = icmp slt T %l, %r } return v; }
template[T:sint_t]
bool op<=(T l, T r) { bool v; llvm { %v = icmp sle T %l, %r } return v; }

template[T:fp_t]
T op+(T l, T r) { T v; llvm { %v = fadd T %l, %r } return v; }
template[T:fp_t]
T op-(T l, T r) { T v; llvm { %v = fsub T %l, %r } return v; }
template[T:fp_t]
T op*(T l, T r) { T v; llvm { %v = fmul T %l, %r } return v; }
template[T:fp_t]
T op/(T l, T r) { T v; llvm { %v = fdiv T %l, %r } return v; }
template[T:fp_t]
T op%%(T l, T r) { T v; llvm { %v = frem T %l, %r } return v; }
template[T:fp_t]
bool op==(T l, T r) { bool v; llvm { %v = fcmp ueq T %l, %r } return v; } // These are all unordered because we can't gaurantee that neither of the operands are QNAN.
template[T:fp_t]
bool op!=(T l, T r) { bool v; llvm { %v = fcmp une T %l, %r } return v; }
template[T:fp_t]
bool op>(T l, T r) { bool v; llvm { %v = fcmp ugt T %l, %r } return v; }
template[T:fp_t]
bool op>=(T l, T r) { bool v; llvm { %v = fcmp uge T %l, %r } return v; }
template[T:fp_t]
bool op<(T l, T r) { bool v; llvm { %v = fcmp ult T %l, %r } return v; }
template[T:fp_t]
bool op<=(T l, T r) { bool v; llvm { %v = fcmp ule T %l, %r } return v; }

// Atomic operations
template[T:integral]
T atomic_xchg(T@ p, T v, AtomicOrdering o = AtomicOrdering.seq_cst) { T r; llvm { %r = atomicrmw xchg T* %p, T %v o } return r; }
template[T:integral]
T atomic_add(T@ p, T v, AtomicOrdering o = AtomicOrdering.seq_cst) { T r; llvm { %r = atomicrmw add T* %p, T %v o } return r; }
template[T:integral]
T atomic_sub(T@ p, T v, AtomicOrdering o = AtomicOrdering.seq_cst) { T r; llvm { %r = atomicrmw sub T* %p, T %v o } return r; }
template[T:integral]
T atomic_and(T@ p, T v, AtomicOrdering o = AtomicOrdering.seq_cst) { T r; llvm { %r = atomicrmw and T* %p, T %v o } return r; }
template[T:integral]
T atomic_nand(T@ p, T v, AtomicOrdering o = AtomicOrdering.seq_cst) { T r; llvm { %r = atomicrmw nand T* %p, T %v o } return r; }
template[T:integral]
T atomic_or(T@ p, T v, AtomicOrdering o = AtomicOrdering.seq_cst) { T r; llvm { %r = atomicrmw or T* %p, T %v o } return r; }
template[T:integral]
T atomic_xor(T@ p, T v, AtomicOrdering o = AtomicOrdering.seq_cst) { T r; llvm { %r = atomicrmw xor T* %p, T %v o } return r; }
template[T:sint_t]
T atomic_max(T@ p, T v, AtomicOrdering o = AtomicOrdering.seq_cst) { T r; llvm { %r = atomicrmw max T* %p, T %v o } return r; }
template[T:sint_t]
T atomic_min(T@ p, T v, AtomicOrdering o = AtomicOrdering.seq_cst) { T r; llvm { %r = atomicrmw min T* %p, T %v o } return r; }
template[T:uint_t]
T atomic_max(T@ p, T v, AtomicOrdering o = AtomicOrdering.seq_cst) { T r; llvm { %r = atomicrmw umax T* %p, T %v o } return r; }
template[T:uint_t]
T atomic_min(T@ p, T v, AtomicOrdering o = AtomicOrdering.seq_cst) { T r; llvm { %r = atomicrmw umin T* %p, T %v o } return r; }

//template[T:integral]
//T atomic_cmpxchg(T* p, T c, T n, AtomicOrdering fail, AtomicOrdering success) { T r; llvm { %r = cmpxchg T* p, T c, T n success fail } return r; }
//template[T:integral]
//T atomic_cmpxchg_weak(T* p, T c, T n, AtomicOrdering fail, AtomicOrdering success) { T r; llvm { %r = cmpxchg weak T* p, T c, T n success fail } return r; }