use std::str::FromStr;

use qiskit_circuit::classical::{expr::{Binary, BinaryOp, Expr, Value, Var}, types::Type};
use uuid::Uuid;
use crate::pointers::{const_ptr_as_ref, mut_ptr_as_ref};
use num_bigint::BigUint;

#[repr(u8)]
pub enum CExprNodeType { 
    Unary = 0, 
    Binary = 1,
    Cast = 2,
    Value = 3,
    Var = 4, 
    Stretch = 5, 
    Index = 6,
}

impl CExprNodeType {
    fn from_expr(expr: &Expr) -> Self {
        match expr {
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

impl CBinaryExprOp {
    fn from_binary_op(op: BinaryOp) -> Self {
        match op {
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

#[repr(u8)]
pub enum CScalarType {
    Bool = 0,
    Duration = 1,
    Float = 2,
    Uint = 3, // TODO: handle, add getter
}

impl CScalarType {
    pub fn from_type(ty: Type) -> Self {
        match ty {
            Type::Bool =>Self::Bool,
            Type::Duration =>Self::Duration,
            Type::Float =>Self::Float,
            Type::Uint(_) =>Self::Uint,
        }
    }
}

#[repr(C)]
pub struct CBinaryExpr {
    pub op: CBinaryExprOp,
    pub left: *const Expr,
    pub right: *const Expr,
    pub ty: CScalarType,
    pub constant: bool,
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn qk_expr_node_type(expr: *const Expr) -> CExprNodeType {
    let expr = unsafe{ const_ptr_as_ref(expr) };

    CExprNodeType::from_expr(expr)
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn qk_expr_binary(expr: *const Expr, out_binary: *mut CBinaryExpr) {
    let expr = unsafe{ const_ptr_as_ref(expr) };

    let Expr::Binary(binary) = expr else {
        panic!("Expecting a Binary expression node")
    };

    let out_binary = unsafe { mut_ptr_as_ref(out_binary) };
    out_binary.op = CBinaryExprOp::from_binary_op(binary.op);
    out_binary.left = &binary.left as *const Expr;
    out_binary.right = &binary.right as *const Expr;
    out_binary.ty = CScalarType::from_type(binary.ty);
    out_binary.constant = binary.constant;    
}

// Builds and returns Var("a") + 3 < 5
#[unsafe(no_mangle)]
unsafe extern "C" fn inner_build_test_expression() -> *mut Expr {
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

// TODO: add qk_expr_free