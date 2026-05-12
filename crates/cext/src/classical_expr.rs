use std::str::FromStr;

use qiskit_circuit::{classical::{expr::{Binary, BinaryOp, Cast, Expr, Stretch, Unary, UnaryOp, Value, Var, Index}, types::Type}, duration::Duration};
use uuid::Uuid;
use crate::pointers::{const_ptr_as_ref, mut_ptr_as_ref};
use num_bigint::BigUint;
use std::ffi::{c_char, CStr, CString};
use num_traits::ToPrimitive;

#[repr(u8)]
pub enum CExprNodeKind { 
    Unary = 0, 
    Binary = 1,
    Cast = 2,
    Value = 3,
    Var = 4, 
    Stretch = 5, 
    Index = 6,
}

impl From<&Expr> for CExprNodeKind {
    fn from(value: &Expr) -> Self {
        match value {
            Expr::Unary(_) => Self::Unary, 
            Expr::Binary(_) => Self::Binary, 
            Expr::Cast(_) => Self::Cast,
            Expr::Index(_) => Self::Index,
            Expr::Stretch(_) => Self::Stretch, 
            Expr::Value(_) => Self::Value,
            Expr::Var(_) => Self::Var,
        }
    }
}

#[repr(u8)]
pub enum CExprType {
    Bool = 0,
    Duration = 1,
    Float = 2,
    Uint = 3,
}

impl From<&Type> for CExprType {
    fn from(value: &Type) -> Self {
        match value {
            Type::Bool => Self::Bool,
            Type::Duration => Self::Duration,
            Type::Float => Self::Float,
            Type::Uint(_) => Self::Uint,
        }
    }
}

#[repr(C)]
pub struct CExprTypeInfo {
    ty: CExprType,
    width: u16,
}

impl CExprTypeInfo {
    fn to_type(&self) -> Type {
        match self.ty {
            CExprType::Bool => Type::Bool,
            CExprType::Duration => Type::Duration,
            CExprType::Float => Type::Float,
            CExprType::Uint => Type::Uint(self.width),
        }
    }
}

impl From<&Type> for CExprTypeInfo {
    fn from(ty: &Type) -> Self {
        match ty {
            Type::Bool => CExprTypeInfo{ty: CExprType::Bool, width: 0},
            Type::Duration => CExprTypeInfo{ty: CExprType::Duration, width: 0},
            Type::Float => CExprTypeInfo{ty: CExprType::Float, width: 0},
            Type::Uint(w) => CExprTypeInfo{ty: CExprType::Uint, width: *w},
        }
    }
}


#[repr(u8)]
pub enum CUnaryOp {
    BitNot = 1, // TODO: keeping it one-based on purpose, to avoid confusion with the convention in Python
    LogicNot = 2,
    Negate = 3,
}

impl From<UnaryOp> for CUnaryOp {
    fn from(value: UnaryOp) -> Self {
        match value { 
        UnaryOp::BitNot => Self::BitNot,
        UnaryOp::LogicNot => Self::LogicNot,
        UnaryOp::Negate => Self::Negate,
        }
    }
}

impl CUnaryOp {
    fn to_unary_op(self) -> UnaryOp {
        match self {
            CUnaryOp::BitNot => UnaryOp::BitNot,
            CUnaryOp::LogicNot => UnaryOp::LogicNot,
            CUnaryOp::Negate => UnaryOp::Negate,
        }
    }
}

#[repr(C)]
pub struct CUnaryExpr {
    pub op: CUnaryOp,
    pub operand: *const Expr,
    pub ty: CExprTypeInfo,
    pub constant: bool,
}

#[repr(u8)]
pub enum CBinaryExprOp {
    BitAnd = 1, // TODO: keeping it one-based on purpose, to avoid confusion with the convention in Python
    BitOr = 2,
    BitXor = 3,
    LogicAnd = 4,
    LogicOr = 5,
    Equal = 6,
    NotEqual = 7,
    Less = 8,
    LessEqual = 9,
    Greater = 10,
    GreaterEqual = 11,
    ShiftLeft = 12,
    ShiftRight = 13,
    Add = 14,
    Sub = 15,
    Mul = 16,
    Div = 17,
}

impl From<BinaryOp> for CBinaryExprOp {
    fn from(value: BinaryOp) -> Self {
        match value {
            BinaryOp::BitAnd => Self::BitAnd,
            BinaryOp::BitOr => Self::BitOr,
            BinaryOp::BitXor => Self::BitXor,
            BinaryOp::LogicAnd => Self::LogicAnd,
            BinaryOp::LogicOr => Self::LogicOr,
            BinaryOp::Equal => Self::Equal,
            BinaryOp::NotEqual => Self::NotEqual,
            BinaryOp::Less => Self::Less,
            BinaryOp::LessEqual => Self::LessEqual,
            BinaryOp::Greater => Self::Greater,
            BinaryOp::GreaterEqual => Self::GreaterEqual,
            BinaryOp::ShiftLeft => Self::ShiftLeft,
            BinaryOp::ShiftRight => Self::ShiftRight,
            BinaryOp::Add => Self::Add,
            BinaryOp::Sub => Self::Sub,
            BinaryOp::Mul => Self::Mul,
            BinaryOp::Div => Self::Div,
        }
    }
}

impl CBinaryExprOp {
    fn to_binary_op(self) -> BinaryOp {
        match self {
            CBinaryExprOp::BitAnd => BinaryOp::BitAnd,
            CBinaryExprOp::BitOr => BinaryOp::BitOr,
            CBinaryExprOp::BitXor => BinaryOp::BitXor,
            CBinaryExprOp::LogicAnd => BinaryOp::LogicAnd,
            CBinaryExprOp::LogicOr => BinaryOp::LogicOr,
            CBinaryExprOp::Equal => BinaryOp::Equal,
            CBinaryExprOp::NotEqual => BinaryOp::NotEqual,
            CBinaryExprOp::Less => BinaryOp::Less,
            CBinaryExprOp::LessEqual => BinaryOp::LessEqual,
            CBinaryExprOp::Greater => BinaryOp::Greater,
            CBinaryExprOp::GreaterEqual => BinaryOp::GreaterEqual,
            CBinaryExprOp::ShiftLeft => BinaryOp::ShiftLeft,
            CBinaryExprOp::ShiftRight => BinaryOp::ShiftRight,
            CBinaryExprOp::Add => BinaryOp::Add,
            CBinaryExprOp::Sub => BinaryOp::Sub,
            CBinaryExprOp::Mul => BinaryOp::Mul,
            CBinaryExprOp::Div => BinaryOp::Div,
        }
    }
}



#[repr(C)]
pub struct CBinaryExpr {
    pub op: CBinaryExprOp,
    pub left: *const Expr,
    pub right: *const Expr,
    pub ty: CExprTypeInfo,
    pub constant: bool,
}

#[repr(C)]
pub struct CCastExpr {
    pub operand: *const Expr,
    pub ty: CExprTypeInfo,
    pub implicit: bool,
    pub constant: bool,
}

#[repr(u8)]
pub enum CValueType {
    Duration = 0,
    Float = 1, 
    Uint = 2, 
}

impl From<&Value> for CValueType {
    fn from(value: &Value) -> Self {
        match value {
            Value::Duration(_) => Self::Duration,
            Value::Float{..} => Self::Float,
            Value::Uint{..} => Self::Uint,
        }
    }
}

#[repr(C)]
pub struct CIndexExpr {
    pub target: *const Expr,
    pub index: *const Expr,
    pub ty: CExprTypeInfo,
    pub constant: bool, 
}

#[repr(u8)]
pub enum CDurationType {
    Dt = 0,
    Ps = 1,
    Ns = 2,
    Us = 3,
    Ms = 4,
    S = 5, 
}
impl From<&Duration> for CDurationType {
    fn from(duration: &Duration) -> Self {
        match duration {
            Duration::dt(_) => Self::Dt,
            Duration::ps(_) => Self::Ps,
            Duration::ns(_) => Self::Ns,
            Duration::us(_) => Self::Us,
            Duration::ms(_) => Self::Ms,
            Duration::s(_) => Self::S,
        }
    }
}

#[repr(C)]
pub struct CDurationInfo {
    pub ty: CDurationType,
    pub time: f64, // TODO: a stopgap for dt, since we can't use unions
}

impl From<&Duration> for CDurationInfo {
    fn from(duration: &Duration) -> Self {
        match duration {
            Duration::dt(v) => CDurationInfo {
                ty: CDurationType::Dt,
                time: *v as f64,
            },
            Duration::ps(v) => CDurationInfo {
                ty: CDurationType::Ps,
                time: *v,
            },
            Duration::ns(v) => CDurationInfo {
                ty: CDurationType::Ns,
                time: *v,
            },
            Duration::us(v) => CDurationInfo {
                ty: CDurationType::Us,
                time: *v,
            },
            Duration::ms(v) => CDurationInfo {
                ty: CDurationType::Ms,
                time: *v,
            },
            Duration::s(v) => CDurationInfo {
                ty: CDurationType::S,
                time: *v,
            },
        }
    }
}

impl CDurationInfo {
    pub fn to_duration(&self) -> Duration {
        match self.ty {
            CDurationType::Dt => Duration::dt(self.time as i64),
            CDurationType::Ps => Duration::ps(self.time),
            CDurationType::Ns => Duration::ns(self.time),
            CDurationType::Us => Duration::us(self.time),
            CDurationType::Ms => Duration::ms(self.time),
            CDurationType::S => Duration::s(self.time),
        }
    }
}


#[unsafe(no_mangle)]
pub unsafe extern "C" fn qk_expr_node_kind(expr: *const Expr) -> CExprNodeKind {
    let expr = unsafe{ const_ptr_as_ref(expr) };

    CExprNodeKind::from(expr)
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn qk_expr_as_binary(expr: *const Expr, out_binary: *mut CBinaryExpr) -> bool {
    let expr = unsafe{ const_ptr_as_ref(expr) };

    let Expr::Binary(binary) = expr else {
        return false;
    }; 

    let out_binary = unsafe { mut_ptr_as_ref(out_binary) };
    out_binary.op = CBinaryExprOp::from(binary.op);
    out_binary.left = &binary.left as *const Expr;
    out_binary.right = &binary.right as *const Expr;
    out_binary.ty = CExprTypeInfo::from(&binary.ty);
    out_binary.constant = binary.constant;
    
    true
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn qk_expr_as_unary(expr: *const Expr, out_unary: *mut CUnaryExpr) -> bool {
    let expr = unsafe { const_ptr_as_ref(expr) };

    let Expr::Unary(unary) = expr else {
        return false;
    };

    let out_unary = unsafe { mut_ptr_as_ref(out_unary) };
    
    out_unary.op = CUnaryOp::from(unary.op);
    out_unary.operand = &unary.operand as *const Expr;
    out_unary.ty = CExprTypeInfo::from(&unary.ty);
    out_unary.constant = unary.constant;
    
    true
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn qk_expr_as_cast(expr: *const Expr, out_cast: *mut CCastExpr) -> bool {
    let expr = unsafe { const_ptr_as_ref(expr) };

    let Expr::Cast(cast) = expr else {
        return false;
    };

    let out_cast = unsafe { mut_ptr_as_ref(out_cast) };
    
    out_cast.operand = &cast.operand as *const Expr;
    out_cast.ty = CExprTypeInfo::from(&cast.ty);
    out_cast.constant = cast.constant;
    out_cast.implicit = cast.implicit;
    
    true
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn qk_expr_as_index(expr: *const Expr, out_index: *mut CIndexExpr) -> bool {
    let expr = unsafe { const_ptr_as_ref(expr) };

    let Expr::Index(index) = expr else {
        return false;
    };

    let out_index = unsafe { mut_ptr_as_ref(out_index) };
    
    out_index.target = &index.target as *const Expr;
    out_index.index = &index.index as *const Expr;
    out_index.ty = CExprTypeInfo::from(&index.ty);
    out_index.constant = index.constant;
    
    true
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn qk_expr_as_value(expr: *const Expr, value: *mut *const Value) -> bool {
    let expr = unsafe { const_ptr_as_ref(expr) };

    let Expr::Value(val) = expr else {
        return false;
    };

    unsafe { *value = val as *const Value };
    
    true
}


#[unsafe(no_mangle)]
pub unsafe extern "C" fn qk_expr_value_type(expr: *const Expr) -> CValueType { 
    let expr = unsafe { const_ptr_as_ref(expr) };
    
    let Expr::Value(value) = expr else {
        panic!("Expected Value expression"); // TODO: change all functions to return bool instead of panicking
    };
    
    CValueType::from(value)
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn qk_expr_value_duration(value: *const Value, out_info: *mut CDurationInfo) -> bool {
    let value = unsafe { const_ptr_as_ref(value) };
    
    let Value::Duration(duration) = value else {
        return false;
    };
    
    unsafe { *out_info = CDurationInfo::from(duration) };
    
    true
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn qk_expr_value_float(value: *const Value, out_val: *mut f64) -> bool {
    let value = unsafe { const_ptr_as_ref(value) };
    
    let Value::Float{raw, ..} = value else { // TODO: what should we do with ty?
        return false;
    };

    unsafe { *out_val = *raw };

    true
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn qk_expr_value_uint(value: *const Value, out_uint: *mut u64) -> bool {
    let value = unsafe { const_ptr_as_ref(value) };
    
    let Value::Uint { raw, .. } = value else { // TODO: what should we do with ty?
        return false;
    };

    let uint = raw.to_u64().expect("BigUint value larger than u64::MAX are not supported currently"); // TODO: is there a better way?
    unsafe{ *out_uint = uint };

    true
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn qk_expr_as_var(expr: *const Expr, out_var: *mut *const Var) -> bool {
    let expr = unsafe { const_ptr_as_ref(expr) };

    let Expr::Var(var) = expr else {
        return false;
    };

    unsafe { *out_var = var as *const Var };
    
    true
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn qk_expr_as_stretch(expr: *const Expr, out_stretch: *mut *const Stretch) -> bool {
    let expr = unsafe { const_ptr_as_ref(expr) };

    let Expr::Stretch(stretch) = expr else {
        return false;
    };

    unsafe { *out_stretch = stretch as *const Stretch };
    
    true
}


#[unsafe(no_mangle)]
pub unsafe extern "C" fn qk_expr_binary_new(op: CBinaryExprOp, left: *const Expr, right: *const Expr, type_info: *const CExprTypeInfo) -> *mut Expr {
    let left = unsafe { const_ptr_as_ref(left) };
    let right = unsafe { const_ptr_as_ref(right) };
    let type_info = unsafe { const_ptr_as_ref(type_info) };

    let binary = Binary{
        op: op.to_binary_op(),
        left: left.clone(),
        right: right.clone(),
        ty: type_info.to_type(),
        constant: left.is_const() && right.is_const(),    
        };

    Box::into_raw(Box::new(Expr::Binary(Box::new(binary))))
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn qk_expr_unary_new(op: CUnaryOp, operand: *const Expr, type_info: *const CExprTypeInfo,) -> *mut Expr {
    let operand = unsafe { const_ptr_as_ref(operand) };
    let type_info = unsafe { const_ptr_as_ref(type_info) };

    let unary = Unary {
        op: op.to_unary_op(),
        operand: operand.clone(),
        ty: type_info.to_type(),
        constant: operand.is_const(),
    };

    Box::into_raw(Box::new(Expr::Unary(Box::new(unary))))
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn qk_expr_cast_new(operand: *const Expr, type_info: *const CExprTypeInfo) -> *mut Expr { 
    let operand = unsafe { const_ptr_as_ref(operand) };
    let type_info = unsafe { const_ptr_as_ref(type_info) };

    let cast = Cast {
        operand: operand.clone(),
        ty: type_info.to_type(),
        constant: operand.is_const(),
        implicit: false, // TODO: we can add qk_expr_cast_implicit_new if needed
    };

    Box::into_raw(Box::new(Expr::Cast(Box::new(cast))))
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn qk_expr_index_new(target: *const Expr, index: *const Expr, type_info: *const CExprTypeInfo) -> *mut Expr { 
    let target = unsafe { const_ptr_as_ref(target) };
    let index = unsafe { const_ptr_as_ref(index) };
    let type_info = unsafe { const_ptr_as_ref(type_info) };

    let index_obj = Index {
        target: target.clone(),
        index: index.clone(),
        ty: type_info.to_type(),
        constant: target.is_const() && index.is_const(),
    };

    Box::into_raw(Box::new(Expr::Index(Box::new(index_obj))))
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn qk_expr_free(expr: *mut Expr) {
    drop( unsafe{Box::from_raw(expr)});
}


#[unsafe(no_mangle)]
pub unsafe extern "C" fn qk_var_new(name: *const c_char, type_info: *const CExprTypeInfo) -> *mut Var {
    let name = unsafe {
        CStr::from_ptr(name)
            .to_str()
            .expect("Invalid UTF-8 character")
            .to_string()
    };

    let type_info = unsafe {const_ptr_as_ref(type_info)} ;

    let var = Var::Standalone { uuid: Uuid::new_v4().as_u128(), name, ty: type_info.to_type() };
    Box::into_raw(Box::new(var))
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn qk_var_name(var: *const Var) -> *mut c_char {
    let var = unsafe { const_ptr_as_ref(var) };
    let Var::Standalone { name, .. } = var else { return std::ptr::null_mut(); };

    CString::new(name.as_str())
        .map_or(std::ptr::null_mut(), |name| name.into_raw())
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn qk_var_type_info(var: *const Var) -> CExprTypeInfo {
    let var = unsafe { const_ptr_as_ref(var) };
    let Var::Standalone { ty, .. } = var else { panic!("Expected a standalone variable") };

    let width = if let Type::Uint(width) = ty {*width} else {0u16};

    CExprTypeInfo{ty: CExprType::from(ty), width: width}
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn qk_var_free(var: *mut Var) {
    let var = unsafe { mut_ptr_as_ref(var) };
    drop( unsafe{ Box::from_raw(var) } );
}


#[unsafe(no_mangle)]
pub unsafe extern "C" fn qk_var_as_expr(var: *const Var) -> *mut Expr {
    let var = unsafe{ const_ptr_as_ref(var) };
    Box::into_raw(Box::new(Expr::Var(var.clone())))
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn qk_stretch_new(name: *const c_char) -> *mut Stretch {
    let name = unsafe {
        CStr::from_ptr(name)
            .to_str()
            .expect("Invalid UTF-8 character")
            .to_string()
    };

    let stretch = Stretch {
        uuid: Uuid::new_v4().as_u128(),
        name,
    };
    
    Box::into_raw(Box::new(stretch))
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn qk_stretch_name(stretch: *const Stretch) -> *mut c_char {
    let stretch = unsafe { const_ptr_as_ref(stretch) };
    
    CString::new(stretch.name.as_str())
        .map_or(std::ptr::null_mut(), |name| name.into_raw())
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn qk_stretch_free(stretch: *mut Stretch) {
    drop(unsafe { Box::from_raw(stretch) });
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn qk_stretch_as_expr(stretch: *const Stretch) -> *mut Expr {
    let stretch = unsafe { const_ptr_as_ref(stretch) };
    Box::into_raw(Box::new(Expr::Stretch(stretch.clone())))
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn qk_value_new_duration(duration: *const CDurationInfo) -> *mut Value {
    let duration = unsafe { const_ptr_as_ref(duration) };

    Box::into_raw(Box::new(Value::Duration(duration.to_duration())))
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn qk_value_new_float(val: f64) -> *mut Value {

    Box::into_raw(Box::new(Value::Float { raw: val, ty: Type::Float }))
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn qk_value_new_uint(val: u64, width: u16) -> *mut Value {
    Box::into_raw(Box::new(Value::Uint { raw: BigUint::from(val), ty: Type::Uint(width) }))
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn qk_value_free(value: *mut Value) {
    drop( unsafe{Box::from_raw(value) } );
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn qk_value_as_expr(value: *const Value) -> *mut Expr {
    let value = unsafe { const_ptr_as_ref(value) };
    Box::into_raw(Box::new(Expr::Value(value.clone())))
}



#[unsafe(no_mangle)]
pub unsafe extern "C" fn inner_build_test_expression() -> *mut Expr {
    let var = Expr::Var(Var::Standalone {
                    uuid: Uuid::new_v4().as_u128(),
                    name: "a".to_owned(),
                    ty: Type::Uint(8),
                });

    let three = Expr::Value(Value::Uint { raw: BigUint::from_str("3").unwrap(), ty: Type::Uint(8) });
    
    let add = Expr::Binary(Box::new(Binary {
        op: BinaryOp::Add,
        left: var,
        right: three,
        ty: Type::Uint(8),
        constant: false,
    }));
    
    let five = Expr::Value(Value::Uint { raw: BigUint::from_str("5").unwrap(), ty: Type::Uint(8) });

    let lt = Expr::Binary(Box::new(Binary {
        op: BinaryOp::LessEqual,
        left: add,
        right: five,
        ty: Type::Uint(8),
        constant: false,
    }));

    Box::into_raw(Box::new(lt))
}
