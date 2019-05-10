/*
 * Copyright (c) 2005, 2008, Oracle and/or its affiliates. All rights reserved.
 * ORACLE PROPRIETARY/CONFIDENTIAL. Use is subject to license terms.
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 */

package sun.management;

import javax.management.openmbean.CompositeType;
import javax.management.openmbean.CompositeData;
import javax.management.openmbean.CompositeDataSupport;
import javax.management.openmbean.OpenDataException;

/**
 * A CompositeData for StackTraceElement for the local management support.
 * This class avoids the performance penalty paid to the
 * construction of a CompositeData use in the local case.
 */
public class StackTraceElementCompositeData extends LazyCompositeData {
    private final StackTraceElement ste;

    private StackTraceElementCompositeData(StackTraceElement ste) {
        this.ste = ste;
    }

    public StackTraceElement getStackTraceElement() {
        return ste;
    }

    public static StackTraceElement from(CompositeData cd) {
        validateCompositeData(cd);

        return new StackTraceElement(getString(cd, CLASS_NAME),
                                     getString(cd, METHOD_NAME),
                                     getString(cd, FILE_NAME),
                                     getInt(cd, LINE_NUMBER));
    }

    public static CompositeData toCompositeData(StackTraceElement ste) {
        StackTraceElementCompositeData cd = new StackTraceElementCompositeData(ste);
        return cd.getCompositeData();
    }

    protected CompositeData getCompositeData() {
        // CONTENTS OF THIS ARRAY MUST BE SYNCHRONIZED WITH
        // stackTraceElementItemNames!
        final Object[] stackTraceElementItemValues = {
            ste.getClassName(),
            ste.getMethodName(),
            ste.getFileName(),
            new Integer(ste.getLineNumber()),
            new Boolean(ste.isNativeMethod()),
        };
        try {
            return new CompositeDataSupport(stackTraceElementCompositeType,
                                            stackTraceElementItemNames,
                                            stackTraceElementItemValues);
        } catch (OpenDataException e) {
            // Should never reach here
            throw new AssertionError(e);
        }
    }

    private static final CompositeType stackTraceElementCompositeType;
    static {
        try {
            stackTraceElementCompositeType = (CompositeType)
                MappedMXBeanType.toOpenType(StackTraceElement.class);
        } catch (OpenDataException e) {
            // Should never reach here
            throw new AssertionError(e);
        }
    }

    // Attribute names
    private static final String CLASS_NAME      = "className";
    private static final String METHOD_NAME     = "methodName";
    private static final String FILE_NAME       = "fileName";
    private static final String LINE_NUMBER     = "lineNumber";
    private static final String NATIVE_METHOD   = "nativeMethod";

    private static final String[] stackTraceElementItemNames = {
        CLASS_NAME,
        METHOD_NAME,
        FILE_NAME,
        LINE_NUMBER,
        NATIVE_METHOD,
    };

    /** Validate if the input CompositeData has the expected
     * CompositeType (i.e. contain all attributes with expected
     * names and types).
     */
    public static void validateCompositeData(CompositeData cd) {
        if (cd == null) {
            throw new NullPointerException("Null CompositeData");
        }

        if (!isTypeMatched(stackTraceElementCompositeType, cd.getCompositeType())) {
            throw new IllegalArgumentException(
                "Unexpected composite type for StackTraceElement");
        }
    }

    private static final long serialVersionUID = -2704607706598396827L;
}
