#define PY_SSIZE_T_CLEAN
#include <Python.h>

#define QISKIT_C_PYTHON_INTERFACE
#include <qiskit.h>


static const char* const CF_OP_NAME[] = {"Box", "BreakLoop", "ContinueLoop", "ForLoop", "IfElse", "Switch", "While"};
static const char* const CF_CONDITION_TYPE[] = {"Bit", "Reg", "Expr"};
static const char* const EXPR_KIND[] = {"Unary", "Binary", "Cast", "Value", "Var", "Stretch", "Index"};
static const char* const EXPR_TYPE[] = {"Bool", "Duration", "Float", "Uint"};
static const char* const DURATION_TYPE[] = {"Dt","Ps", "Ns", "Us", "Ms", "S"}; 

void print_circuit(const QkCircuit *, unsigned indent, const QkControlFlowInstruction*);

void inspect_register(const QkClassicalRegister *creg, unsigned indent) {
    char *reg_name = qk_classical_register_name(creg);

    printf("%*sCREG: %s\n", indent, "", reg_name);

    qk_str_free(reg_name);
}

void inspect_expr(const QkExprNode *expr_node, unsigned indent) {
    QkExprNodeKind kind = qk_expr_node_kind(expr_node);
    printf("%*sEXPR type: %s\n", indent, "", EXPR_KIND[kind]);

    switch (kind) {
        case QkExprNodeKind_Unary:
            QkUnaryExprInfo unary = qk_expr_unary_info(expr_node);
            
            printf("%*s UNARY: Op %d, Type %s, Const %d\n", indent, "", 
                unary.op, 
                EXPR_TYPE[unary.ty.ty], 
                unary.constant);

            inspect_expr(unary.operand, indent + 2);
            break;
        case QkExprNodeKind_Binary:
            QkBinaryExprInfo binary = qk_expr_binary_info(expr_node);

            printf("%*s BINARY: Op %d, Type %s, Const %d\n", indent, "", 
                binary.op, 
                EXPR_TYPE[binary.ty.ty], 
                binary.constant);
            
            inspect_expr(binary.left, indent + 2);
            inspect_expr(binary.right, indent + 2);
            break;
        case QkExprNodeKind_Cast:
            QkCastExprInfo cast = qk_expr_cast_info(expr_node);

            printf("%*s CAST: Type %s, implicit %d, Const %d\n", indent, "", 
                EXPR_TYPE[cast.ty.ty],
                cast.implicit,
                cast.constant);
            
            inspect_expr(cast.operand, indent + 2);
            break;
        case QkExprNodeKind_Index:
            QkIndexExprInfo index = qk_expr_index_info(expr_node);

            printf("%*s INDEX: Type %s\n", indent, "", 
                EXPR_TYPE[index.ty.ty]);

            inspect_expr(index.target, indent + 2);
            inspect_expr(index.index, indent + 2);

            break;
        case QkExprNodeKind_Value:
            const QkValue *value = qk_expr_as_value(expr_node);
            QkValueType value_type = qk_value_type(value);
            
            printf("%*s VALUE: Type %s, ", indent, "", EXPR_TYPE[value_type]);
            switch (value_type) {
                case QkValueType_Duration:
                    QkDurationInfo duration_info = qk_value_duration_info(value);
                    if (duration_info.ty == QkDurationType_Dt)
                        printf("Dt %ld\n", duration_info.value.dt);
                    else
                        printf("%s %lf\n", DURATION_TYPE[duration_info.ty], duration_info.value.time);
                    break;
                case QkValueType_Float:
                    double duration = qk_value_float(value);
                    printf("%lf\n", duration);
                    break;
                case QkValueType_Uint:
                    uint64_t val = qk_value_uint(value);
                    printf("%ld\n", val);
                    break; 
            }

            break;
        case QkExprNodeKind_Var:
            const QkVar *var = qk_expr_as_var(expr_node);
            char* name = qk_var_name(var);
            QkExprTypeInfo type_info = qk_var_type_info(var);
            printf("%*s VAR: Name %s, Type %s", indent, "", 
                name,
                EXPR_TYPE[type_info.ty]);
            if ( type_info.ty == QkExprType_Uint)
                printf("(%d)\n", type_info.width);
            else
                printf("\n");
            qk_str_free(name);
            break;
        case QkExprNodeKind_Stretch:
            const QkStretch *stretch = qk_expr_as_stretch(expr_node);
            name = qk_stretch_name(stretch);
            printf("%*s STRETCH: Name %s\n", indent, "", name);
            qk_str_free(name);
            break;
    }
}

void inspect_condition(const QkControlFlowInstruction *cf_inst, unsigned indent) {
    QkControlFlowKind cf_type = qk_control_flow_kind(cf_inst);
    
    if ( cf_type != QkControlFlowKind_IfElse && cf_type != QkControlFlowKind_While)
        return;

    QkConditionType condition_type = qk_control_flow_condition_type(cf_inst);

    printf("%*s condition type: %s\n", indent, "", CF_CONDITION_TYPE[condition_type]);

    switch (condition_type) {
        case QkConditionType_ClBit:
            QkConditionBitInfo cond_bit_info = qk_control_flow_condition_bit_info(cf_inst);

            printf("%*s Bit: %d Condition: %d\n", indent + 2, "", 
                cond_bit_info.clbit,
                cond_bit_info.condition);
            
            break;
        case QkConditionType_ClReg:
            QkConditionRegInfo cond_reg_info = qk_control_flow_condition_reg_info(cf_inst);

            inspect_register(cond_reg_info.creg, indent + 2);
            printf("%*s COND: %ld\n", indent + 2, "", cond_reg_info.condition);

            break;
        case QkConditionType_Expr:
            const QkExprNode *expr = qk_control_flow_condition_expr(cf_inst);
            inspect_expr(expr, indent + 2);
            break;
    }
}

void inspect_box(const QkControlFlowInstruction *cf_inst, unsigned indent) {
    QkBoxDurationType duration_type = qk_control_flow_box_duration_type(cf_inst);
    switch (duration_type) {
    case QkBoxDurationType_NoDuration: 
        printf("%*s No Duration info\n", indent, "");
        break;
    case QkBoxDurationType_Duration: 
        QkDurationInfo duration_info = qk_control_flow_box_duration_info(cf_inst);
        printf("%*s Duration type: %s Value: ", indent, "", DURATION_TYPE[duration_info.ty]);
        if (duration_info.ty == QkDurationType_Dt)
            printf("%ld\n", duration_info.value.dt);
        else
            printf("%lf\n", duration_info.value.time);
        break;
    case QkBoxDurationType_Expr:
        const QkExprNode *expr = qk_control_flow_box_duration_expr(cf_inst);
        inspect_expr(expr, indent + 2);        
        break;
    }
}

void inspect_for_loop(const QkControlFlowInstruction *cf_inst, unsigned indent) {
    size_t const* elements;
    size_t num_elements = qk_control_flow_loop_collection(cf_inst, &elements);
    printf("%*s Elements: ", indent, "");
    for (size_t i = 0; i < num_elements; i++)
        printf("%ld ", elements[i]);
    printf("\n");

    char *symbol; 
    int64_t index = qk_control_flow_loop_symbol(cf_inst, &symbol);

    if ( symbol != NULL ) {
        printf("%*s Symbol: %s\n", indent, "", symbol);
        qk_str_free(symbol);
    }
    if ( index >= 0) {
        printf("%*s Index: %ld\n", indent, "", index);
    }
}

void inspect_switch(const QkControlFlowInstruction *cf_inst, unsigned indent) {
    QkConditionType target_type = qk_control_flow_switch_target_type(cf_inst);

    switch (target_type) {
    case QkConditionType_ClBit:
        int64_t bit = qk_control_flow_switch_target_bit(cf_inst);
        printf("%*sBit: %ld\n", indent, "", bit);
        break;
    case QkConditionType_ClReg:
        const QkClassicalRegister *creg = qk_control_flow_switch_target_register(cf_inst);
        inspect_register(creg, indent + 2);
        break;
    case QkConditionType_Expr:
        const QkExprNode *expr = qk_control_flow_switch_target_expr(cf_inst);
        inspect_expr(expr, indent + 2);
        break;    
    }

    uint32_t num_cases = qk_control_flow_switch_num_cases(cf_inst);
    for(uint32_t case_idx = 0; case_idx < num_cases; case_idx++) {
        printf("%*sCASE: ", indent, "");
        if (qk_control_flow_switch_is_case_default(cf_inst, case_idx) ) 
            printf("Default");
        else {
            QkSwitchCaseLabels labels;
            qk_control_flow_switch_case_labels(cf_inst, case_idx, &labels);
            for (size_t label = 0; label < labels.num_labels; label++) {
                printf("%ld ", labels.labels[label]);
            }
            qk_control_flow_switch_case_labels_clear(&labels);
        }
        printf("\n");
    }
}

void inspect_control_flow(const QkControlFlowInstruction *cf_inst, unsigned indent) { 
    QkControlFlowKind cf_type = qk_control_flow_kind(cf_inst);
    printf("%*s CONTROL FLOW: %s\n", indent, "[ ]", CF_OP_NAME[cf_type]);

    switch (cf_type) {
        case QkControlFlowKind_Box:
            inspect_box(cf_inst, indent + 2);
            break;
        case QkControlFlowKind_BreakLoop:
            break;
        case QkControlFlowKind_ContinueLoop:
            break;
        case QkControlFlowKind_ForLoop:
            inspect_for_loop(cf_inst, indent + 2);
            break;
        case QkControlFlowKind_IfElse:
        case QkControlFlowKind_While:
            inspect_condition(cf_inst, indent + 2);
            break;
        case QkControlFlowKind_Switch:
            inspect_switch(cf_inst, indent + 2);
            break;
    }


    uint32_t num_blocks = qk_control_flow_num_blocks(cf_inst);

    for (uint32_t block = 0; block < num_blocks; block++) {
        const QkCircuit *block_circuit = qk_control_flow_block_circuit(cf_inst, block);

        printf("%*sBlock #%d\n", indent, "", block);
        
        print_circuit(block_circuit, indent + 2, cf_inst);
    }
}

void print_circuit(const QkCircuit *circuit, unsigned indent, const QkControlFlowInstruction* parent_cf) {
    size_t num_instructions = qk_circuit_num_instructions(circuit);

    for (size_t inst_idx = 0; inst_idx < num_instructions; inst_idx++) { 
        QkCircuitInstruction inst;
        qk_circuit_get_instruction(circuit, inst_idx, &inst);

        QkOperationKind kind = qk_circuit_instruction_kind(circuit, inst_idx);

        if (kind == QkOperationKind_ControlFlow) {
            QkControlFlowInstruction *cf_inst = qk_circuit_get_control_flow_instruction(circuit, inst_idx, parent_cf);

            inspect_control_flow(cf_inst, indent + 2);

            qk_control_flow_instruction_free(cf_inst);
        } else {
            printf("%*s%s ", indent, " ", inst.name);

            // Print qubit/clbit indices with mapping to the top-level circuit taken into account
            const uint32_t *qubit_mapping = parent_cf ? qk_control_flow_qubit_map(parent_cf) : NULL;
            for (uint32_t qubit = 0; qubit < inst.num_qubits; qubit++) {
                uint32_t mapped_qubit = qubit_mapping ? qubit_mapping[inst.qubits[qubit]] : inst.qubits[qubit];
                printf("%d%s", mapped_qubit, qubit < inst.num_qubits - 1 ? ", " : "\n");
            }
            
            const uint32_t *clbit_mapping = parent_cf ? qk_control_flow_clbit_map(parent_cf) : NULL;
            for (uint32_t clbit = 0; clbit < inst.num_clbits; clbit++) {
                uint32_t mapped_clbit = clbit_mapping ? clbit_mapping[inst.clbits[clbit]] : inst.clbits[clbit];
                printf("%d%s", mapped_clbit, clbit < inst.num_clbits - 1 ? ", " : "\n");
            }
        }

        qk_circuit_instruction_clear(&inst);
    }
}

static PyObject *traverse_circuit(PyObject *self, PyObject *ob) {

    QkCircuit *circuit = qk_circuit_borrow_from_python(ob);

    print_circuit(circuit, 2, NULL);

    return Py_None;
}

/* Method table */
static PyMethodDef my_python_ext_funcs[] = {
    {"traverse_circuit", (PyCFunction)traverse_circuit, METH_O, ""},
    {NULL, NULL, 0, NULL}
};

/* Module definition (PEP 3121/384 style) */
static struct PyModuleDef my_qiskit_extmodule = {
    PyModuleDef_HEAD_INIT,
    "my_python_ext",
    "A tiny C extension with add and dot",
    -1,                 // per-interpreter state size, -1 for global state
    my_python_ext_funcs
};

/* Module init function */
PyMODINIT_FUNC PyInit_my_python_ext(void) {
    return PyModule_Create(&my_qiskit_extmodule);
}
