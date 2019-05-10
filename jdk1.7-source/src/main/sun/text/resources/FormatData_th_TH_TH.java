/*
 * Copyright (c) 2002, 2005, Oracle and/or its affiliates. All rights reserved.
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

/*
 */

package sun.text.resources;

import java.util.ListResourceBundle;

/*
 * This class implements the th_TH_TH requirement that native Thai
 * digits be used in the corresponding locale.
 *
 * @author John O'Conner
 * @since 1.4.1
 *
 */

public class FormatData_th_TH_TH extends ListResourceBundle {
    /**
     * Overrides ListResourceBundle
     */
    protected final Object[][] getContents() {
        return new Object[][] {

            { "NumberElements",
                new String[] {
                    ".", // decimal separator
                    ",", // group (thousands) separator
                    ";", // list separator
                    "%", // percent sign
                    "\u0E50", // native 0 digit
                    "#", // pattern digit
                    "-", // minus sign
                    "E", // exponential
                    "\u2030", // per mille
                    "\u221e", // infinity
                    "\ufffd" // NaN
                }
            },

        };
    }
}
