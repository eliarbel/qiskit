#include "common.h"
#include <complex.h>
#include <math.h>
#include <qiskit.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

static int test_var(void) {
    int result = Ok;

    QkVar *var_bool = qk_var_new("v",  &(QkExprTypeInfo){QkExprType_Bool, 0});
    QkExprTypeInfo type_info = qk_var_type_info(var_bool);
    if ( type_info.ty != QkExprType_Bool ) {
        fprintf(stderr, "Bool var type mismatch: expected %d, got %d\n", QkExprType_Bool, type_info.ty);
        result = EqualityError;
        goto clear_var_bool;
    }

    QkVar *var_float = qk_var_new("v",  &(QkExprTypeInfo){QkExprType_Float, 0});
    type_info = qk_var_type_info(var_float);
    if ( type_info.ty != QkExprType_Float ) {
        fprintf(stderr, "Float var type mismatch: expected %d, got %d\n", QkExprType_Float, type_info.ty);
        result = EqualityError;
        goto clear_var_float;
    }

    QkVar *var_duration = qk_var_new("v",  &(QkExprTypeInfo){QkExprType_Duration, 0});
    type_info = qk_var_type_info(var_duration);
    if ( type_info.ty != QkExprType_Duration ) {
        fprintf(stderr, "Duration var type mismatch: expected %d, got %d\n", QkExprType_Duration, type_info.ty);
        result = EqualityError;
        goto clear_var_duration;
    }

    QkVar *var_uint = qk_var_new("my_var",  &(QkExprTypeInfo){QkExprType_Uint, 7});
    type_info = qk_var_type_info(var_uint);
    if ( type_info.ty != QkExprType_Uint || type_info.width != 7 ) {
        fprintf(stderr, "Uint var type/width mismatch: expected type=%d width=7, got type=%d width=%u\n",
                QkExprType_Uint, type_info.ty, type_info.width);
        result = EqualityError;
        goto clear_var_uint;
    }

    QkExprNode *var_expr = qk_var_as_expr(var_uint);
    QkExprNodeKind kind = qk_expr_node_kind(var_expr);
    if (kind != QkExprNodeKind_Var) {
        fprintf(stderr, "Expr node kind mismatch: expected %d, got %d\n", QkExprNodeKind_Var, kind);
        result = EqualityError;
        goto clear_var_expr;
    }

    const QkVar *extracted_var = NULL;
    if (!qk_expr_as_var(var_expr, &extracted_var)) {
        fprintf(stderr, "Failed to extract var from expression\n");
        result = RuntimeError;
        goto clear_var_expr;
    }

    char *name = qk_var_name(extracted_var);
    if (strcmp(name, "my_var") != 0) {
        fprintf(stderr, "Var name mismatch: expected 'my_var', got '%s'\n", name);
        result = EqualityError;
    }
    qk_str_free(name);

clear_var_expr:
    qk_expr_free(var_expr);
clear_var_uint:
    qk_var_free(var_uint);
clear_var_duration:
    qk_var_free(var_duration);
clear_var_float:
    qk_var_free(var_float);
clear_var_bool:
    qk_var_free(var_bool);

    return result;
}

static int test_stretch(void) {
    int result = Ok;

    QkStretch *stretch = qk_stretch_new("my_stretch");

    char *name = qk_stretch_name(stretch);
    if (strcmp(name, "my_stretch") != 0) {
        fprintf(stderr, "Stretch name mismatch: expected 'my_stretch', got '%s'\n", name);
        result = EqualityError;
        goto clear_stretch;
    }

    QkExprNode *stretch_expr = qk_stretch_as_expr(stretch);
    QkExprNodeKind kind = qk_expr_node_kind(stretch_expr);
    if (kind != QkExprNodeKind_Stretch) {
        fprintf(stderr, "Stretch expr node kind mismatch: expected %d, got %d\n", QkExprNodeKind_Stretch, kind);
        result = EqualityError;
        goto clear_stretch_expr;
    }

    const QkStretch *extracted_stretch = NULL;
    if (!qk_expr_as_stretch(stretch_expr, &extracted_stretch)) {
        fprintf(stderr, "Failed to extract stretch from expression\n");
        result = RuntimeError;
        goto clear_stretch_expr;
    }

    char *extracted_name = qk_stretch_name(extracted_stretch);
    if (strcmp(extracted_name, "my_stretch") != 0) {
        fprintf(stderr, "Extracted stretch name mismatch: expected 'my_stretch', got '%s'\n", extracted_name);
        result = EqualityError;
    }

    qk_str_free(extracted_name);
clear_stretch_expr:
    qk_expr_free(stretch_expr);
clear_stretch:
    qk_str_free(name);
    qk_stretch_free(stretch);

    return result;
}

static int test_value(void) {
    int result = Ok;

    QkValue *float_val = qk_value_new_float(3.14);
    QkExprNode *float_expr = qk_value_as_expr(float_val);
    QkExprNodeKind kind = qk_expr_node_kind(float_expr);
    if (kind != QkExprNodeKind_Value) {
        fprintf(stderr, "Float value expr node kind mismatch: expected %d, got %d\n", QkExprNodeKind_Value, kind);
        result = EqualityError;
        goto clear_float_expr;
    }

    const QkValue *extracted_val = NULL;
    if (!qk_expr_as_value(float_expr, &extracted_val)) {
        fprintf(stderr, "Failed to extract float value from expression\n");
        result = RuntimeError;
        goto clear_float_expr;
    }

    double extracted_float;
    if (!qk_expr_value_float(extracted_val, &extracted_float)) {
        fprintf(stderr, "Failed to extract float from value\n");
        result = RuntimeError;
        goto clear_float_expr;
    }

    if (extracted_float != 3.14) {
        fprintf(stderr, "Float value mismatch: expected 3.14, got %f\n", extracted_float);
        result = EqualityError;
        goto clear_float_expr;
    }

    QkValue *uint_val = qk_value_new_uint(42, 8);
    QkExprNode *uint_expr = qk_value_as_expr(uint_val);
    const QkValue *extracted_uint_val = NULL;
    if (!qk_expr_as_value(uint_expr, &extracted_uint_val)) {
        fprintf(stderr, "Failed to extract uint value from expression\n");
        result = RuntimeError;
        goto clear_uint_expr;
    }

    uint64_t extracted_uint;
    if (!qk_expr_value_uint(extracted_uint_val, &extracted_uint)) {
        fprintf(stderr, "Failed to extract uint from value\n");
        result = RuntimeError;
        goto clear_uint_expr;
    }

    if (extracted_uint != 42) {
        fprintf(stderr, "Uint value mismatch: expected 42, got %lu\n", (unsigned long)extracted_uint);
        result = EqualityError;
        goto clear_uint_expr;
    }

    QkDurationInfo dur_info = {
        .ty = QkDurationType_Ns,
        .time = 100.0
    };
    QkValue *dur_val = qk_value_new_duration(&dur_info);
    QkExprNode *dur_expr = qk_value_as_expr(dur_val);
    const QkValue *extracted_dur_val = NULL;
    if (!qk_expr_as_value(dur_expr, &extracted_dur_val)) {
        fprintf(stderr, "Failed to extract duration value from expression\n");
        result = RuntimeError;
        goto clear_dur_expr;
    }

    QkDurationInfo extracted_dur_info;
    if (!qk_expr_value_duration(extracted_dur_val, &extracted_dur_info)) {
        fprintf(stderr, "Failed to extract duration from value\n");
        result = RuntimeError;
        goto clear_dur_expr;
    }

    if (extracted_dur_info.ty != QkDurationType_Ns ||
        extracted_dur_info.time != 100.0) {
        fprintf(stderr, "Duration value mismatch: expected type=%d time=100.0, got type=%d time=%f\n",
                QkDurationType_Ns, extracted_dur_info.ty, extracted_dur_info.time);
        result = EqualityError;
    }

clear_dur_expr:
    qk_expr_free(dur_expr);
    qk_value_free(dur_val);
clear_uint_expr:
    qk_expr_free(uint_expr);
    qk_value_free(uint_val);
clear_float_expr:
    qk_expr_free(float_expr);
    qk_value_free(float_val);

    return result;
}

static int test_expr_structs(void) {
    int result = Ok;
    
    QkExprTypeInfo type_info = {QkExprType_Uint, 8};
    QkVar *var1 = qk_var_new("V1", &type_info);
    QkVar *var2 = qk_var_new("V2", &type_info);
    QkExprNode *v1Expr = qk_var_as_expr(var1);
    QkExprNode *v2Expr = qk_var_as_expr(var2);

    // Test Binary expressions
    for (uint8_t op = 1; op <= 17; op++) {
        QkExprNode *expr = qk_expr_binary_new(op, v1Expr, v2Expr, &type_info);
        
        QkBinaryExpr binary;
        if (!qk_expr_as_binary(expr, &binary)) {
            fprintf(stderr, "Failed to extract binary expression for operator %u\n", op);
            result = RuntimeError;
            qk_expr_free(expr);
            goto cleanup;
        }
        
        if (binary.op != op) {
            fprintf(stderr, "Binary operator mismatch for op %u: expected %u, got %u\n",
                    op, op, binary.op);
            result = EqualityError;
            qk_expr_free(expr);
            goto cleanup;
        }
        
        if (binary.left != v1Expr || binary.right != v2Expr) {
            fprintf(stderr, "Binary operand mismatch\n");
            result = EqualityError;
            qk_expr_free(expr);
            goto cleanup;
        }
        
        if (binary.ty.ty != type_info.ty || binary.ty.width != type_info.width) {
            fprintf(stderr, "Binary type mismatch for op %u: expected type=%u width=%u, got type=%u width=%u\n",
                    op, type_info.ty, type_info.width, binary.ty.ty, binary.ty.width);
            result = EqualityError;
            qk_expr_free(expr);
            goto cleanup;
        }
        
        if (binary.constant) {
            fprintf(stderr, "Binary constant flag mismatch for op %u: expected false, got true\n", op);
            result = EqualityError;
            qk_expr_free(expr);
            goto cleanup;
        }
        
        qk_expr_free(expr);
    }

    // Test Unary expressions
    for (uint8_t op = 1; op <= 3; op++) {
        QkExprNode *expr = qk_expr_unary_new(op, v1Expr, &type_info);
        
        QkUnaryExpr unary;
        if (!qk_expr_as_unary(expr, &unary)) {
            fprintf(stderr, "Failed to extract unary expression for operator %u\n", op);
            result = RuntimeError;
            qk_expr_free(expr);
            goto cleanup;
        }
        
        if (unary.op != op) {
            fprintf(stderr, "Unary operator mismatch for op %u: expected %u, got %u\n",
                    op, op, unary.op);
            result = EqualityError;
            qk_expr_free(expr);
            goto cleanup;
        }
        
        if (unary.operand != v1Expr) {
            fprintf(stderr, "Unary operand mismatch for op %u: operand=%p (expected %p)\n",
                    op, (void*)unary.operand, (void*)v1Expr);
            result = EqualityError;
            qk_expr_free(expr);
            goto cleanup;
        }
        
        if (unary.ty.ty != type_info.ty || unary.ty.width != type_info.width) {
            fprintf(stderr, "Unary type mismatch for op %u: expected type=%u width=%u, got type=%u width=%u\n",
                    op, type_info.ty, type_info.width, unary.ty.ty, unary.ty.width);
            result = EqualityError;
            qk_expr_free(expr);
            goto cleanup;
        }
        
        if (unary.constant) {
            fprintf(stderr, "Unary constant flag mismatch for op %u: expected false, got true\n", op);
            result = EqualityError;
            qk_expr_free(expr);
            goto cleanup;
        }
        
        qk_expr_free(expr);
    }

    // Test Cast expression
    QkExprTypeInfo target_type = {QkExprType_Float, 0};
    QkExprNode *cast_expr = qk_expr_cast_new(v1Expr, &target_type);
    
    QkCastExpr cast;
    if (!qk_expr_as_cast(cast_expr, &cast)) {
        fprintf(stderr, "Failed to extract cast expression\n");
        result = RuntimeError;
        qk_expr_free(cast_expr);
        goto cleanup;
    }
    
    if (cast.operand != v1Expr) {
        fprintf(stderr, "Cast operand mismatch: operand=%p (expected %p)\n",
                (void*)cast.operand, (void*)v1Expr);
        result = EqualityError;
        qk_expr_free(cast_expr);
        goto cleanup;
    }
    
    if (cast.ty.ty != target_type.ty || cast.ty.width != target_type.width) {
        fprintf(stderr, "Cast type mismatch: expected type=%u width=%u, got type=%u width=%u\n",
                target_type.ty, target_type.width, cast.ty.ty, cast.ty.width);
        result = EqualityError;
        qk_expr_free(cast_expr);
        goto cleanup;
    }
    
    if (cast.implicit) {
        fprintf(stderr, "Cast implicit flag mismatch: expected false, got true\n");
        result = EqualityError;
        qk_expr_free(cast_expr);
        goto cleanup;
    }
    
    qk_expr_free(cast_expr);

    // Test Index expression
    QkValue *index_val = qk_value_new_uint(5, 8);
    QkExprNode *index_val_expr = qk_value_as_expr(index_val);
    QkExprNode *index_expr = qk_expr_index_new(v1Expr, index_val_expr, &type_info);
    
    QkIndexExpr index;
    if (!qk_expr_as_index(index_expr, &index)) {
        fprintf(stderr, "Failed to extract index expression\n");
        result = RuntimeError;
        qk_expr_free(index_expr);
        qk_expr_free(index_val_expr);
        qk_value_free(index_val);
        goto cleanup;
    }
    
    if (index.target != v1Expr) {
        fprintf(stderr, "Index target mismatch: target=%p (expected %p)\n",
                (void*)index.target, (void*)v1Expr);
        result = EqualityError;
        qk_expr_free(index_expr);
        qk_expr_free(index_val_expr);
        qk_value_free(index_val);
        goto cleanup;
    }
    
    if (index.index != index_val_expr) {
        fprintf(stderr, "Index index mismatch: index=%p (expected %p)\n",
                (void*)index.index, (void*)index_val_expr);
        result = EqualityError;
        qk_expr_free(index_expr);
        qk_expr_free(index_val_expr);
        qk_value_free(index_val);
        goto cleanup;
    }
    
    if (index.ty.ty != type_info.ty || index.ty.width != type_info.width) {
        fprintf(stderr, "Index type mismatch: expected type=%u width=%u, got type=%u width=%u\n",
                type_info.ty, type_info.width, index.ty.ty, index.ty.width);
        result = EqualityError;
        qk_expr_free(index_expr);
        qk_expr_free(index_val_expr);
        qk_value_free(index_val);
        goto cleanup;
    }
    
    qk_expr_free(index_expr);
    qk_expr_free(index_val_expr);
    qk_value_free(index_val);

cleanup:
    qk_expr_free(v2Expr);
    qk_expr_free(v1Expr);
    qk_var_free(var2);
    qk_var_free(var1);

    return result;
}


QkExprNode *inner_build_test_expression();
static int test_expression(void) {
    QkExprNode *expr = inner_build_test_expression();
    printf("NODE TYPE %d\n", qk_expr_node_kind(expr));

    return RuntimeError;
}

int test_classical_expr(void) {
    int num_failed = 0;
    num_failed += RUN_TEST(test_var);
    num_failed += RUN_TEST(test_stretch);
    num_failed += RUN_TEST(test_value);
    num_failed += RUN_TEST(test_expr_structs);
    num_failed += RUN_TEST(test_expression);

    fflush(stderr);
    fprintf(stderr, "=== Number of failed subtests: %i\n", num_failed);

    return num_failed;
}

