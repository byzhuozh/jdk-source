/*
 * Copyright (c) 2007, Oracle and/or its affiliates. All rights reserved.
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

package sun.print;

import javax.print.attribute.PrintRequestAttribute;
import java.awt.Frame;

/**
 * Class DialogOwner is a printing attribute class that identifies
 * the window that owns the print dialog.
 *
 * <P>
 * <B>IPP Compatibility:</B> This is not an IPP attribute.
 * <P>
 *
 */
public final class DialogOwner
    implements PrintRequestAttribute {

    private Frame dlgOwner;

    /**
     * Construct a new dialog type selection enumeration value with the
     * given integer value.
     *
     * @param  value  Integer value.
     */
    public DialogOwner(Frame frame) {
        dlgOwner = frame;
    }


    /**
     * Returns the string table for class DialogOwner.
     */
    public Frame getOwner() {
        return dlgOwner;
    }


    /**
     * Get the printing attribute class which is to be used as the "category"
     * for this printing attribute value.
     * <P>
     * For class DialogOwner the category is class
     * DialogOwner itself.
     *
     * @return  Printing attribute class (category), an instance of class
     *          {@link java.lang.Class java.lang.Class}.
     */
    public final Class getCategory() {
        return DialogOwner.class;
    }


    /**
     * Get the name of the category of which this attribute value is an
     * instance.
     * <P>
     * For class DialogOwner the category name is
     * <CODE>"dialog-owner"</CODE>.
     *
     * @return  Attribute category name.
     */
    public final String getName() {
        return "dialog-owner";
    }

}
