package org.omg.Dynamic;


/**
* org/omg/Dynamic/Parameter.java .
* Generated by the IDL-to-Java compiler (portable), version "3.2"
* from ../../../../src/share/classes/org/omg/PortableInterceptor/Interceptors.idl
* Wednesday, February 2, 2011 6:12:11 PM GMT-08:00
*/

public final class Parameter implements org.omg.CORBA.portable.IDLEntity
{
  public org.omg.CORBA.Any argument = null;
  public org.omg.CORBA.ParameterMode mode = null;

  public Parameter ()
  {
  } // ctor

  public Parameter (org.omg.CORBA.Any _argument, org.omg.CORBA.ParameterMode _mode)
  {
    argument = _argument;
    mode = _mode;
  } // ctor

} // class Parameter
