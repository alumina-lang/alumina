// The C side of c_abi.alu.
#include <stdint.h>
#include <stddef.h>

static const uint8_t DATA[4] = {1, 2, 3, 4};
const uint8_t *c_data(void) { return DATA; }

typedef struct { uint32_t a; uint32_t b; } Pair32;
typedef struct { uint16_t a; uint8_t b; } Small;
typedef struct { uint8_t a; uint8_t b; uint8_t c; } Bytes3;
typedef struct { float a; int32_t b; } MixF;
typedef struct { double a; int32_t b; } DI;
typedef struct { int64_t a; int8_t b; } IB;
typedef struct { uint8_t a; double b; } BD;
typedef struct { float a; float b; float c; } F3;
typedef struct { double a; double b; double c; double d; } D4;
typedef struct { uint64_t a; uint64_t b; } W2;
typedef struct { const uint8_t * a; size_t b; } PL;
typedef struct { uint64_t a; uint32_t b; uint64_t c; uint8_t d; uint64_t e; } Big;

Pair32 c_make_Pair32(int32_t k) { return k == 5 ? (Pair32){ .a = 15, .b = 18 } : (Pair32){0}; }
int c_check_Pair32(Pair32 x, int32_t k, Pair32 y) { return k == 9 && x.a == 22 && x.b == 25 && y.a == 29 && y.b == 32; }
int c_callback_Pair32(Pair32 (*f)(Pair32, int32_t, Pair32)) { Pair32 r = f((Pair32){ .a = 36, .b = 39 }, 11, (Pair32){ .a = 43, .b = 46 }); return r.a == 50 && r.b == 53; }

Small c_make_Small(int32_t k) { return k == 5 ? (Small){ .a = 15, .b = 18 } : (Small){0}; }
int c_check_Small(Small x, int32_t k, Small y) { return k == 9 && x.a == 22 && x.b == 25 && y.a == 29 && y.b == 32; }
int c_callback_Small(Small (*f)(Small, int32_t, Small)) { Small r = f((Small){ .a = 36, .b = 39 }, 11, (Small){ .a = 43, .b = 46 }); return r.a == 50 && r.b == 53; }

Bytes3 c_make_Bytes3(int32_t k) { return k == 5 ? (Bytes3){ .a = 15, .b = 18, .c = 21 } : (Bytes3){0}; }
int c_check_Bytes3(Bytes3 x, int32_t k, Bytes3 y) { return k == 9 && x.a == 22 && x.b == 25 && x.c == 28 && y.a == 29 && y.b == 32 && y.c == 35; }
int c_callback_Bytes3(Bytes3 (*f)(Bytes3, int32_t, Bytes3)) { Bytes3 r = f((Bytes3){ .a = 36, .b = 39, .c = 42 }, 11, (Bytes3){ .a = 43, .b = 46, .c = 49 }); return r.a == 50 && r.b == 53 && r.c == 56; }

MixF c_make_MixF(int32_t k) { return k == 5 ? (MixF){ .a = 15.5f, .b = 18 } : (MixF){0}; }
int c_check_MixF(MixF x, int32_t k, MixF y) { return k == 9 && x.a == 22.5f && x.b == 25 && y.a == 29.5f && y.b == 32; }
int c_callback_MixF(MixF (*f)(MixF, int32_t, MixF)) { MixF r = f((MixF){ .a = 36.5f, .b = 39 }, 11, (MixF){ .a = 43.5f, .b = 46 }); return r.a == 50.5f && r.b == 53; }

DI c_make_DI(int32_t k) { return k == 5 ? (DI){ .a = 15.5, .b = 18 } : (DI){0}; }
int c_check_DI(DI x, int32_t k, DI y) { return k == 9 && x.a == 22.5 && x.b == 25 && y.a == 29.5 && y.b == 32; }
int c_callback_DI(DI (*f)(DI, int32_t, DI)) { DI r = f((DI){ .a = 36.5, .b = 39 }, 11, (DI){ .a = 43.5, .b = 46 }); return r.a == 50.5 && r.b == 53; }

IB c_make_IB(int32_t k) { return k == 5 ? (IB){ .a = 15, .b = 18 } : (IB){0}; }
int c_check_IB(IB x, int32_t k, IB y) { return k == 9 && x.a == 22 && x.b == 25 && y.a == 29 && y.b == 32; }
int c_callback_IB(IB (*f)(IB, int32_t, IB)) { IB r = f((IB){ .a = 36, .b = 39 }, 11, (IB){ .a = 43, .b = 46 }); return r.a == 50 && r.b == 53; }

BD c_make_BD(int32_t k) { return k == 5 ? (BD){ .a = 15, .b = 18.5 } : (BD){0}; }
int c_check_BD(BD x, int32_t k, BD y) { return k == 9 && x.a == 22 && x.b == 25.5 && y.a == 29 && y.b == 32.5; }
int c_callback_BD(BD (*f)(BD, int32_t, BD)) { BD r = f((BD){ .a = 36, .b = 39.5 }, 11, (BD){ .a = 43, .b = 46.5 }); return r.a == 50 && r.b == 53.5; }

F3 c_make_F3(int32_t k) { return k == 5 ? (F3){ .a = 15.5f, .b = 18.5f, .c = 21.5f } : (F3){0}; }
int c_check_F3(F3 x, int32_t k, F3 y) { return k == 9 && x.a == 22.5f && x.b == 25.5f && x.c == 28.5f && y.a == 29.5f && y.b == 32.5f && y.c == 35.5f; }
int c_callback_F3(F3 (*f)(F3, int32_t, F3)) { F3 r = f((F3){ .a = 36.5f, .b = 39.5f, .c = 42.5f }, 11, (F3){ .a = 43.5f, .b = 46.5f, .c = 49.5f }); return r.a == 50.5f && r.b == 53.5f && r.c == 56.5f; }

D4 c_make_D4(int32_t k) { return k == 5 ? (D4){ .a = 15.5, .b = 18.5, .c = 21.5, .d = 24.5 } : (D4){0}; }
int c_check_D4(D4 x, int32_t k, D4 y) { return k == 9 && x.a == 22.5 && x.b == 25.5 && x.c == 28.5 && x.d == 31.5 && y.a == 29.5 && y.b == 32.5 && y.c == 35.5 && y.d == 38.5; }
int c_callback_D4(D4 (*f)(D4, int32_t, D4)) { D4 r = f((D4){ .a = 36.5, .b = 39.5, .c = 42.5, .d = 45.5 }, 11, (D4){ .a = 43.5, .b = 46.5, .c = 49.5, .d = 52.5 }); return r.a == 50.5 && r.b == 53.5 && r.c == 56.5 && r.d == 59.5; }

W2 c_make_W2(int32_t k) { return k == 5 ? (W2){ .a = 15, .b = 18 } : (W2){0}; }
int c_check_W2(W2 x, int32_t k, W2 y) { return k == 9 && x.a == 22 && x.b == 25 && y.a == 29 && y.b == 32; }
int c_callback_W2(W2 (*f)(W2, int32_t, W2)) { W2 r = f((W2){ .a = 36, .b = 39 }, 11, (W2){ .a = 43, .b = 46 }); return r.a == 50 && r.b == 53; }

PL c_make_PL(int32_t k) { return k == 5 ? (PL){ .a = c_data(), .b = 18 } : (PL){0}; }
int c_check_PL(PL x, int32_t k, PL y) { return k == 9 && x.a == c_data() && x.b == 25 && y.a == c_data() && y.b == 32; }
int c_callback_PL(PL (*f)(PL, int32_t, PL)) { PL r = f((PL){ .a = c_data(), .b = 39 }, 11, (PL){ .a = c_data(), .b = 46 }); return r.a == c_data() && r.b == 53; }

Big c_make_Big(int32_t k) { return k == 5 ? (Big){ .a = 15, .b = 18, .c = 21, .d = 24, .e = 27 } : (Big){0}; }
int c_check_Big(Big x, int32_t k, Big y) { return k == 9 && x.a == 22 && x.b == 25 && x.c == 28 && x.d == 31 && x.e == 34 && y.a == 29 && y.b == 32 && y.c == 35 && y.d == 38 && y.e == 41; }
int c_callback_Big(Big (*f)(Big, int32_t, Big)) { Big r = f((Big){ .a = 36, .b = 39, .c = 42, .d = 45, .e = 48 }, 11, (Big){ .a = 43, .b = 46, .c = 49, .d = 52, .e = 55 }); return r.a == 50 && r.b == 53 && r.c == 56 && r.d == 59 && r.e == 62; }
